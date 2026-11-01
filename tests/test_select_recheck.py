"""Which notebooks a pull request rechecks, without Lean or Glitnir."""

import tempfile
import unittest
from pathlib import Path

from scripts.select_recheck import ALL, imported_modules, recheck_matrix, select_notebooks

LAKEFILE = "".join(
    f'[[lean_lib]]\nname = "{name}"\nsrcDir = "examples/{folder}"\n'
    for name, folder in [("A", "x"), ("B", "x"), ("C", "y"), ("D", "y")]
)
IMPORTS = {"A": "import Mathlib\n", "B": "import Mathlib\nimport A\n", "C": "import B -- c\n", "D": ""}


class SelectTests(unittest.TestCase):
    """B imports A, C imports B, D stands alone."""

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        (self.root / "lakefile.toml").write_text(LAKEFILE)
        for name, text in IMPORTS.items():
            folder = self.root / ("examples/x" if name in "AB" else "examples/y")
            folder.mkdir(parents=True, exist_ok=True)
            (folder / f"{name}.lean").write_text(text + "\ntheorem t : True := trivial\n")

    def select(self, *paths: str) -> object:
        return select_notebooks(paths, self.root)

    def test_matrix_covers_all_selected_notebooks_once(self) -> None:
        """Serial full-suite time must not accumulate in one six-hour job."""
        self.assertEqual(recheck_matrix(ALL, self.root), {"notebook": ["A", "B", "C", "D"]})
        self.assertEqual(recheck_matrix("C A C", self.root), {"notebook": ["A", "C"]})
        self.assertEqual(recheck_matrix("", self.root), {"notebook": []})

    def test_matrix_refuses_unknown_names_and_excludes_certificate_libraries(self) -> None:
        """A typo cannot silently skip checks; opt-in certificates are not notebooks."""
        with (self.root / "lakefile.toml").open("a") as config:
            config.write('[[lean_lib]]\nname = "Heavy"\nsrcDir = "certificates"\n')
        self.assertEqual(recheck_matrix(ALL, self.root), {"notebook": ["A", "B", "C", "D"]})
        with self.assertRaisesRegex(ValueError, "Unknown"):
            recheck_matrix("Heavy", self.root)

    def test_results_and_docs_need_nothing(self) -> None:
        """Results files, docs and the gallery code trigger no recheck."""
        self.assertEqual(
            self.select("examples/x/A.glitnir.json", "README.md", "AGENTS.md", "gallery/x.js"),
            [],
        )
        self.assertEqual(self.select(), [])

    def test_walkthroughs_are_never_selected(self) -> None:
        """Walkthroughs are not notebooks of this project: nothing rechecks them."""
        self.assertEqual(
            self.select(
                "walkthroughs/eth/EthWalkthrough.lean",
                "walkthroughs/eth/outline.json",
                "walkthroughs/eth/lakefile.toml",
                "walkthroughs/eth/lean-toolchain",
            ),
            [],
        )

    def test_one_notebook(self) -> None:
        """An isolated notebook rechecks alone, results file or not."""
        self.assertEqual(self.select("examples/y/D.lean", "examples/y/D.glitnir.json"), ["D"])

    def test_importers_follow_transitively(self) -> None:
        """Changing A rechecks B, which C imports."""
        self.assertEqual(self.select("examples/x/A.lean"), ["A", "B", "C"])
        self.assertEqual(self.select("examples/x/B.lean"), ["B", "C"])

    def test_sorted_and_deduplicated(self) -> None:
        """Several changes give each notebook once, sorted."""
        self.assertEqual(self.select("examples/y/D.lean", "examples/x/B.lean"), ["B", "C", "D"])

    def test_shared_files_recheck_everything(self) -> None:
        """Pins, requirements, the recheck tooling and its workflow select all."""
        for path in (
            "lean-toolchain",
            "lake-manifest.json",
            "lakefile.toml",
            "scripts/gallery/requirements.txt",
            "scripts/glitnir_release.py",
            "scripts/recheck-requirements.txt",
            "scripts/recheck.py",
            "scripts/select_recheck.py",
            ".github/workflows/recheck.yml",
        ):
            self.assertEqual(self.select("examples/y/D.lean", path), ALL, path)

    def test_unknown_lean_source_rechecks_everything(self) -> None:
        """A deleted or helper source under examples cannot be traced."""
        self.assertEqual(self.select("examples/x/Gone.lean"), ALL)

    def test_other_workflows_and_scripts_are_ignored(self) -> None:
        """Only the recheck's own files matter."""
        self.assertEqual(
            self.select(".github/workflows/gallery.yml", "scripts/build_gallery.py"), []
        )

    def test_import_parsing(self) -> None:
        """Imports are read from the header, with comments and several per line."""
        self.assertEqual(
            imported_modules("-- hi\nimport A.B -- c\nimport  C D\n\n/-! doc -/\nimport E\n"),
            {"A.B", "C", "D"},
        )


if __name__ == "__main__":
    unittest.main()

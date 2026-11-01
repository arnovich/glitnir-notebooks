"""Bundle validation must fail rather than silently lose corpus coverage."""

import json
import tempfile
import unittest
from pathlib import Path

from conftest import add_certificate_library, make_corpus, results_for

from scripts.check_bundles import check_bundles


class BundleTests(unittest.TestCase):
    """Validate the inventory and each notebook's saved Glitnir results."""

    def test_complete_corpus(self) -> None:
        """A configured notebook with results for its source passes."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root)
            self.assertEqual(check_bundles(root), (1, 1))

    def test_missing_results_are_named(self) -> None:
        """Every configured notebook needs its committed results file."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root).with_suffix(".glitnir.json").unlink()
            with self.assertRaisesRegex(
                ValueError, r"missing Glitnir results .*Example\.glitnir\.json"
            ):
                check_bundles(root)

    def test_results_for_other_source(self) -> None:
        """Results recorded before the notebook changed are refused."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            notebook.write_text(notebook.read_text() + "-- edited\n")
            with self.assertRaisesRegex(ValueError, "other source"):
                check_bundles(root)

    def test_crlf_source_matches_like_glitnir(self) -> None:
        """Glitnir hashes saved source with CRLF read as LF."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            notebook.write_bytes(notebook.read_bytes().replace(b"\n", b"\r\n"))
            self.assertEqual(check_bundles(root), (1, 1))

    def test_malformed_results(self) -> None:
        """Other formats, broken JSON and malformed claims are refused."""
        for change in ("format", "json", "claim", "environment"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as d:
                root = Path(d)
                notebook = make_corpus(root)
                results = results_for(notebook.read_text())
                if change == "format":
                    results["format"] = "gimle.forseti.notebook/v1"
                elif change == "claim":
                    del results["claims"][0]["prefix_sha256"]
                elif change == "environment":
                    results["environment"] = {}
                text = "{" if change == "json" else json.dumps(results)
                notebook.with_suffix(".glitnir.json").write_text(text)
                with self.assertRaisesRegex(ValueError, "invalid Glitnir results"):
                    check_bundles(root)

    def test_linked_results_are_refused(self) -> None:
        """A results file linked from elsewhere is not a committed result."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "repo"
            notebook = make_corpus(root)
            results = notebook.with_suffix(".glitnir.json")
            outside = Path(directory) / "outside.json"
            results.rename(outside)
            results.symlink_to(outside)
            with self.assertRaises(ValueError):
                check_bundles(root)

    def test_only_limits_results_not_inventory(self) -> None:
        """A local preview may skip results, never the inventory."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            notebook.with_suffix(".glitnir.json").unlink()
            self.assertEqual(check_bundles(root, only=[]), (0, 0))
            with self.assertRaises(ValueError):
                check_bundles(root, only=["Missing"])
            notebook.with_name("Omitted.lean").write_text("-- omitted\n")
            with self.assertRaises(ValueError):
                check_bundles(root, only=[])

    def test_unconfigured_source(self) -> None:
        """An omitted Lake target cannot silently reduce coverage."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            notebook.with_name("Omitted.lean").write_text("-- omitted\n")
            with self.assertRaises(ValueError):
                check_bundles(root)

    def test_duplicate_name(self) -> None:
        """Two topics cannot ambiguously identify one notebook."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            (root / notebook.name).write_bytes(notebook.read_bytes())
            with self.assertRaises(ValueError):
                check_bundles(root)

    def test_build_dependencies_are_not_examples(self) -> None:
        """Do not discover dependency sources in .lake."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root)
            dependency = root / ".lake/packages/Dependency.lean"
            dependency.parent.mkdir(parents=True)
            dependency.write_text("-- dependency\n")
            self.assertEqual(check_bundles(root), (1, 1))

    def test_walkthroughs_are_not_notebooks(self) -> None:
        """Walkthroughs have no results and are neither inventoried nor configured."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root)
            folder = root / "walkthroughs/fixture"
            folder.mkdir(parents=True)
            (folder / "Fixture.lean").write_text("theorem t : True := trivial\n")
            (folder / "lakefile.toml").write_text('name = "fixture"\n')
            (folder / "outline.json").write_text("{}")
            self.assertEqual(check_bundles(root), (1, 1))
            lakefile = root / "lakefile.toml"
            base = lakefile.read_text()
            for extra in (
                '[[lean_lib]]\nname = "Fixture"\nsrcDir = "walkthroughs/fixture"\n',
                '[[lean_lib]]\nname = "Fixture"\nsrcDir = "./walkthroughs/fixture"\n',
            ):
                with self.subTest(extra=extra):
                    lakefile.write_text(base + extra)
                    with self.assertRaisesRegex(ValueError, "not notebooks of the root"):
                        check_bundles(root)
            lakefile.write_text(
                base.replace(
                    "[[lean_lib]]",
                    '[[require]]\nname = "fixture"\npath = "walkthroughs/fixture"\n\n[[lean_lib]]',
                )
            )
            with self.assertRaisesRegex(ValueError, "Lake dependency fixture"):
                check_bundles(root)

    def test_repository_lakefile_names_no_walkthrough(self) -> None:
        """This repository's own Lake configuration leaves walkthroughs out."""
        root = Path(__file__).resolve().parents[1]
        text = (root / "lakefile.toml").read_text()
        self.assertNotIn("walkthroughs", text)

    def test_certificate_library_is_not_a_notebook(self) -> None:
        """An opt-in certificate library is accepted and not taken for a notebook."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root)
            add_certificate_library(root)
            self.assertEqual(check_bundles(root), (1, 1))

    def test_certificate_library_is_not_a_default_target(self) -> None:
        """A certificate library must stay opt-in."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root)
            add_certificate_library(root, default=True)
            with self.assertRaises(ValueError):
                check_bundles(root)

    def test_certificate_library_needs_its_root(self) -> None:
        """A certificate library without its root module is refused."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root)
            add_certificate_library(root)
            (root / "certificates/Certified.lean").unlink()
            with self.assertRaises(ValueError):
                check_bundles(root)

    def test_internal_symlink_is_rejected(self) -> None:
        """Match the runtime's refusal of linked sources, even inside the repo."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            original = notebook.rename(notebook.with_suffix(".original"))
            notebook.symlink_to(original)
            with self.assertRaises(ValueError):
                check_bundles(root)


if __name__ == "__main__":
    unittest.main()

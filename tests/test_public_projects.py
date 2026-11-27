"""Public notebook checks must be independent of the restricted collection."""

import tempfile
import unittest
from pathlib import Path

from conftest import add_public_corpus, make_corpus

from scripts.build_gallery import inventory
from scripts.check_bundles import check_bundles, notebook_paths
from scripts.select_recheck import recheck_matrix, select_notebooks


class PublicProjectTests(unittest.TestCase):
    """Keep complete inventory coverage while routing each project separately."""

    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.private = make_corpus(self.root)
        self.public = add_public_corpus(self.root)

    def test_both_projects_are_inventoried(self) -> None:
        """A nested public project cannot silently disappear from the gallery."""
        self.assertEqual(set(notebook_paths(self.root)), {self.private, self.public})
        self.assertEqual(check_bundles(self.root), (2, 2))
        self.assertEqual(set(inventory(self.root)), {self.private, self.public})

    def test_public_pins_recheck_only_the_public_project(self) -> None:
        """Changing public dependencies must not launch private builds."""
        for path in (
            "public/lakefile.toml",
            "public/lake-manifest.json",
            "public/lean-toolchain",
        ):
            with self.subTest(path=path):
                self.assertEqual(select_notebooks([path], self.root), ["PublicExample"])

    def test_public_source_is_selected(self) -> None:
        """A changed migrated notebook still receives a genuine recheck."""
        changed = self.public.relative_to(self.root).as_posix()
        self.assertEqual(select_notebooks([changed], self.root), ["PublicExample"])

    def test_nested_inventory_is_strict(self) -> None:
        """An unconfigured public notebook must fail the combined inventory."""
        self.public.with_name("Forgotten.lean").write_text("theorem t : True := trivial\n")
        with self.assertRaisesRegex(ValueError, "inventory"):
            notebook_paths(self.root)

    def test_names_must_be_unique_across_projects(self) -> None:
        """Shared names would make selection and gallery routes ambiguous."""
        config = self.root / "public/lakefile.toml"
        config.write_text(config.read_text().replace("PublicExample", "Example"))
        self.public.rename(self.public.with_name("Example.lean"))
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            notebook_paths(self.root)

    def test_private_dependency_is_rejected_in_public_project(self) -> None:
        """The new project must not inherit the dependency it was split from."""
        manifest = self.root / "public/lake-manifest.json"
        manifest.write_text(manifest.read_text().replace('"mathlib"', '"forseti"'))
        with self.assertRaisesRegex(ValueError, "public.*depend|Public.*depend"):
            notebook_paths(self.root)

    def test_private_pins_do_not_invalidate_public_notebooks(self) -> None:
        """The two projects have independent dependency environments."""
        self.assertEqual(select_notebooks(["lake-manifest.json"], self.root), ["Example"])

    def test_gallery_keeps_existing_topic_routes(self) -> None:
        """A moved source retains its public page URL."""
        from unittest.mock import patch
        from scripts.build_gallery import prepare_notebook

        cache = self.root / "cache"
        cache.mkdir()
        with patch("scripts.build_gallery._saved_notebook") as saved:
            with patch("scripts.build_gallery.saved_snapshot", return_value={"views": []}):
                with patch("scripts.build_gallery._figures", return_value=[]):
                    entry = prepare_notebook(self.public, self.root, cache)
        self.assertEqual(entry["html"], "basics/PublicExample.html")
        self.assertEqual(entry["path"], "public/examples/basics/PublicExample.lean")

    def test_public_ci_selects_only_reproducible_notebooks(self) -> None:
        """Public runners never fetch private dependencies for legacy snapshots."""
        self.assertEqual(
            recheck_matrix("all", self.root, public_only=True),
            {"notebook": ["PublicExample"]},
        )
        self.assertEqual(recheck_matrix("Example", self.root, public_only=True), {"notebook": []})

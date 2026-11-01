"""Preserve author-owned decision content while refreshing checked proofs."""

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from conftest import curated_decision
from scripts.decision_refresh import PreservationError, refresh_decision
from scripts.recheck import Recheck, text_sha256


class PreservationTests(unittest.TestCase):
    """A refresh changes the theorem, not its curated surrounding source."""

    def test_preserves_prose_shared_prelude_and_four_identity_checks(self) -> None:
        """The issue #91 shape retains all author-owned bytes."""
        old, candidate = curated_decision()
        result = refresh_decision(old, "bound", candidate)
        self.assertEqual(result, old.replace("  trivial", "  exact True.intro"))
        self.assertEqual(result.count("example : @forseti"), 4)
        self.assertEqual(result.count("def forsetiTime"), 1)

    def test_preserves_annotations_with_inline_definitions(self) -> None:
        """A non-shared decision also preserves its doc and prose comments."""
        old, candidate = curated_decision(shared=False)
        self.assertEqual(
            refresh_decision(old, "bound", candidate),
            old.replace("  trivial", "  exact True.intro"),
        )

    def test_refuses_changed_supporting_definitions(self) -> None:
        """A proof checked with different context cannot reuse the old context."""
        for shared in (False, True):
            with self.subTest(shared=shared):
                old, candidate = curated_decision(shared)
                candidate = candidate.replace("forsetiTime : Nat := 0", "forsetiTime : Nat := 9")
                with self.assertRaisesRegex(PreservationError, "forsetiTime"):
                    refresh_decision(old, "bound", candidate)

    def test_comment_contents_cannot_impersonate_commands(self) -> None:
        """Nested prose and string literals never delimit a theorem."""
        old, candidate = curated_decision()
        old = old.replace(
            "Authored prose.",
            "Authored prose. /- Nested. -/\nend Decided_bound\ntheorem fake : False := by sorry",
        )
        self.assertEqual(
            refresh_decision(old, "bound", candidate),
            old.replace("  trivial", "  exact True.intro"),
        )

    def test_refuses_to_drop_an_authored_comment_inside_the_proof(self) -> None:
        """Ambiguous edits are refused rather than silently deleted."""
        old, candidate = curated_decision()
        old = old.replace("  trivial", "  -- Author proof note.\n  trivial")
        with self.assertRaisesRegex(PreservationError, "comment"):
            refresh_decision(old, "bound", candidate)

    def test_a_comment_quoted_in_a_string_does_not_preserve_the_comment(self) -> None:
        """A text occurrence inside a literal is not an authored comment."""
        old, candidate = curated_decision()
        old = old.replace("  trivial", "  -- Author proof note.\n  trivial")
        candidate = candidate.replace(
            "  exact True.intro",
            '  let note := "-- Author proof note."\n  exact True.intro',
        )
        with self.assertRaisesRegex(PreservationError, "comment"):
            refresh_decision(old, "bound", candidate)

    def test_duplicate_proof_comments_are_not_silently_dropped(self) -> None:
        """Every occurrence of an authored comment is accounted for."""
        old, candidate = curated_decision()
        old = old.replace("  trivial", "  -- Note.\n  -- Note.\n  trivial")
        candidate = candidate.replace("  exact True.intro", "  -- Note.\n  exact True.intro")
        with self.assertRaisesRegex(PreservationError, "comment"):
            refresh_decision(old, "bound", candidate)

    def test_refuses_missing_or_ambiguous_namespaces(self) -> None:
        """No guess is made about unsupported source structure."""
        old, candidate = curated_decision()
        with self.assertRaises(PreservationError):
            refresh_decision(old + old, "bound", candidate)
        with self.assertRaises(PreservationError):
            refresh_decision(old, "other", candidate)

    def test_literal_whitespace_is_not_ignored(self) -> None:
        """Different string values must not compare as matching definitions."""
        old, candidate = curated_decision(shared=False)
        old = old.replace("forsetiTime : Nat := 0", 'forsetiTime : String := "a  b"')
        candidate = candidate.replace("forsetiTime : Nat := 0", 'forsetiTime : String := "a b"')
        with self.assertRaisesRegex(PreservationError, "forsetiTime"):
            refresh_decision(old, "bound", candidate)

    def test_a_refutation_can_refresh_a_proof_without_losing_context(self) -> None:
        """Changed outcomes still replace only the generated declaration."""
        old, candidate = curated_decision()
        candidate = candidate.replace(
            "theorem bound : True := by\n  exact True.intro",
            "theorem bound_refuted : ¬ False := by\n  exact fun h => h",
        )
        self.assertEqual(
            refresh_decision(old, "bound", candidate),
            old.replace(
                "theorem bound : True := by\n  trivial",
                "theorem bound_refuted : ¬ False := by\n  exact fun h => h",
            ),
        )

    def test_real_ns_t3_blocks_keep_all_twelve_identity_examples(self) -> None:
        """Use the actual issue #91 blocks, with a harmless new proof comment."""
        source = (Path(__file__).resolve().parents[1] / "examples/galerkin/NS_T3.lean").read_text()
        for name, shared in (
            ("below_10", "5a37f797df5f"), ("below_12", "5a37f797df5f"),
            ("in_enstrophy_ball", "05178f0d2091"),
        ):
            with self.subTest(name=name):
                namespace = f"DecidedShared_{shared}"
                definitions = source.split(f"namespace {namespace}\n", 1)[1]
                definitions = definitions.split(f"end {namespace}", 1)[0]
                opening, closing = f"namespace Decided_{name}", f"end Decided_{name}"
                block = opening + source.split(opening, 1)[1].split(closing, 1)[0] + closing
                candidate = block.replace(f"open {namespace}", definitions.strip())
                candidate = "\n".join(
                    line for line in candidate.split("\n")
                    if not line.startswith("example : @forseti")
                )
                candidate = candidate.replace(":= by\n", ":= by\n  -- Refreshed proof.\n", 1)
                expected_block = block.replace(":= by\n", ":= by\n  -- Refreshed proof.\n", 1)
                refreshed = refresh_decision(source, name, candidate)
                self.assertEqual(refreshed, source.replace(block, expected_block, 1))
                self.assertEqual(refreshed.count("example : @forseti"), 12)


class RecheckPreservationTests(unittest.TestCase):
    """Exercise the source-writing path without running Lean or Glitnir."""

    def test_refresh_keeps_shared_prelude_before_the_decision(self) -> None:
        """Accepting a fresh candidate restores the original source location."""
        old, candidate = curated_decision()
        self._run_refresh(old, candidate, old.replace("  trivial", "  exact True.intro"))

    def test_refused_refresh_restores_the_original_file(self) -> None:
        """Definition changes leave the authored notebook intact and reported."""
        old, candidate = curated_decision()
        candidate = candidate.replace("forsetiTime : Nat := 0", "forsetiTime : Nat := 9")
        self._run_refresh(old, candidate, old, refused=True)

    def test_failed_verification_restores_the_original_file(self) -> None:
        """The exact curated block must check before it is accepted."""
        old, candidate = curated_decision()
        self._run_refresh(old, candidate, old, refused=True, failure="verification")

    def test_failed_receipt_save_restores_the_original_file(self) -> None:
        """Source and receipt cannot be left half-accepted."""
        old, candidate = curated_decision()
        self._run_refresh(old, candidate, old, refused=True, failure="receipt")

    def test_concurrent_author_edit_is_not_rolled_back(self) -> None:
        """A provider finishing after an external edit cannot erase that edit."""
        old, candidate = curated_decision()
        self._run_refresh(
            old, candidate, "-- Author edit during the run.\n",
            refused=True, failure="external",
        )

    def test_failed_run_does_not_claim_an_external_receipt(self) -> None:
        """A failed provider cannot own a receipt written while it was running."""
        old, candidate = curated_decision()
        self._run_refresh(old, candidate, old, refused=True, failure="external-receipt")

    def _run_refresh(
        self, old: str, candidate: str, expected: str,
        refused: bool = False, failure: str | None = None,
    ) -> None:
        """Drive a temporary notebook through the real decision acceptance loop."""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Example.lean"
            path.write_text(old)
            records = {"decisions": {"key": {"outcome": {
                "block": old.split("\n", 1)[1], "theorem": "Decided_bound.bound",
            }}}}
            path.with_suffix(".glitnir.json").write_text(json.dumps(records))
            original_records = json.loads(json.dumps(records))
            card = {"key": "key", "name": "bound", "line": 1, "end_line": 1, "status": "stale"}
            checker = Recheck.__new__(Recheck)
            checker.path, checker.force_decisions = path, set()
            checker.done, checker.problems = [], []
            checker.service = SimpleNamespace(
                snapshot=lambda: {"decisions": [card]},
                decision_candidate=lambda key: {
                    "sha256": text_sha256(path.read_text()),
                    "insert_after_line": 1,
                    "block": candidate,
                },
            )
            verdict = {"status": "checked", "message": "checked", "axioms": [], "type": "True"}

            def run_candidate(*args: object) -> dict:
                """Emulate the provider replacing its saved decision entry."""
                records["decisions"]["key"]["outcome"]["block"] = candidate
                path.with_suffix(".glitnir.json").write_text(json.dumps(records))
                return {
                    "status": "candidate",
                    "outcome": json.loads(json.dumps(records["decisions"]["key"]["outcome"])),
                    "verification": None,
                }

            def restore(key: str, previous: dict | None, owned: dict) -> None:
                """Emulate a guarded receipt rollback without Glitnir installed."""
                current = json.loads(path.with_suffix(".glitnir.json").read_text())
                self.assertEqual(current["decisions"][key], owned)
                current["decisions"][key] = previous
                path.with_suffix(".glitnir.json").write_text(json.dumps(current))

            with (
                patch.object(Recheck, "_run_card", side_effect=run_candidate) as run,
                patch.object(Recheck, "_check_refresh", return_value=verdict) as verify,
                patch.object(Recheck, "_save_refresh") as save,
                patch.object(Recheck, "_restore_refresh", side_effect=restore),
            ):
                if failure == "verification":
                    verify.side_effect = PreservationError("Preserved block did not check.")
                if failure == "receipt":
                    save.side_effect = PreservationError("Receipt changed during verification.")
                if failure == "external":
                    def external_edit(*args: object) -> dict:
                        """Emulate an author saving new source during the run."""
                        path.write_text(expected)
                        return {"status": "unknown"}
                    run.side_effect = external_edit
                if failure == "external-receipt":
                    def external_receipt(*args: object) -> dict:
                        """Emulate another process saving a receipt during failure."""
                        records["decisions"]["key"]["outcome"]["block"] = "external receipt"
                        path.with_suffix(".glitnir.json").write_text(json.dumps(records))
                        return {"status": "stale", "run_error": "Provider failed."}
                    run.side_effect = external_receipt
                checker.decide()
                if not refused:
                    block = verify.call_args.args[2]
                    self.assertEqual(block.count("example : @forseti"), 4)
                    self.assertIn("namespace DecidedShared_fixture", block)
                    self.assertEqual(save.call_args.args[2:], (block, verdict))
                    self.assertEqual(
                        expected.split("\n")[1:1 + len(block.split("\n"))],
                        block.split("\n"),
                    )
            self.assertEqual(path.read_text(), expected)
            self.assertEqual(bool(checker.problems), refused)
            if failure == "external-receipt":
                current = json.loads(path.with_suffix(".glitnir.json").read_text())
                self.assertEqual(
                    current["decisions"]["key"]["outcome"]["block"], "external receipt"
                )
            elif refused and failure != "external":
                self.assertEqual(
                    json.loads(path.with_suffix(".glitnir.json").read_text()), original_records
                )


@unittest.skipUnless(importlib.util.find_spec("glitnir"), "Glitnir records API not installed")
class RecordsApiTests(unittest.TestCase):
    """Exercise real receipt validation separately from the no-Lean unit tests."""

    def test_preserved_receipt_is_accepted_and_prior_receipt_can_be_restored(self) -> None:
        """Use the canonical loader/writer and the real accepted-block predicate."""
        from glitnir.notebook.check_records import decision_status, load_records, saved_decisions

        root = Path(__file__).resolve().parents[1]
        records = json.loads((root / "examples/galerkin/NS_T3.glitnir.json").read_text())
        key, entry = next(
            (key, value) for key, value in records["decisions"].items()
            if value["outcome"]["block"]
        )
        old, candidate = curated_decision()
        entry["outcome"]["block"] = candidate
        entry["outcome"]["theorem"] = "Decided_bound.bound"
        records["decisions"] = {key: entry}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Example.lean"
            refreshed = refresh_decision(old, "bound", candidate)
            path.write_text(refreshed)
            path.with_suffix(".glitnir.json").write_text(json.dumps(records))
            previous = saved_decisions(load_records(path))[key]
            checker = Recheck.__new__(Recheck)
            checker.path = path
            block = refreshed.split("\n", 1)[1].split("end Decided_bound", 1)[0]
            block += "end Decided_bound"
            checker._save_refresh(key, previous, block, previous["verification"])
            saved = saved_decisions(load_records(path))[key]
            self.assertEqual(decision_status(saved, refreshed, 1, "f" * 64), "accepted")
            checker._restore_refresh(key, previous, saved)
            self.assertEqual(saved_decisions(load_records(path))[key], previous)

    def test_verification_uses_glitnir_and_rejects_unchecked_blocks(self) -> None:
        """The recheck cannot accept a rejected verdict from the proof authority."""
        checker = Recheck.__new__(Recheck)
        checker.path = Path("Example.lean")
        with patch("glitnir.lean.project_checking.check_candidate", return_value={
            "status": "rejected", "message": "Identity check failed.",
        }) as check:
            with self.assertRaisesRegex(PreservationError, "Identity check failed"):
                checker._check_refresh("a" * 64, 7, "exact preserved block", "bound")
            self.assertEqual(check.call_args.kwargs["block"], "exact preserved block")
            self.assertEqual(check.call_args.kwargs["insert_after_line"], 7)


if __name__ == "__main__":
    unittest.main()

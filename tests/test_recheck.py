"""The recheck tool's source edits and summaries, without Lean or Glitnir."""

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

from scripts.recheck import (
    Recheck,
    busy,
    claim_counts,
    decided_block,
    markdown,
    other_environment,
    status_changes,
    to_rerun,
    with_block,
    withheld_from,
    without_lines,
)

BLOCK = "namespace Decided_bound\n\ntheorem bound : True := by\n  trivial\n\nend Decided_bound"
NOTEBOOK = f"import Mathlib\n-- @decide bound : some goal\n{BLOCK}\n\n-- @decide other : goal\n"


def claim(name: str, status: str, **extra: object) -> dict:
    """Return a saved claim with only the fields the summary reads."""
    return {"name": name, "status": status, **extra}


class BlockTests(unittest.TestCase):
    """Find and replace an earlier decision's block as Accept inserts it."""

    def test_finds_the_block_right_after_its_directive(self) -> None:
        """The span covers the namespace through its end line."""
        lines = NOTEBOOK.split("\n")
        self.assertEqual(decided_block(lines, 2, "bound"), (2, 8))

    def test_allows_blank_lines_before_the_generated_block(self) -> None:
        """Formatting whitespace does not hide an existing generated block."""
        lines = NOTEBOOK.split("\n")
        self.assertIsNone(decided_block(lines, 2, "other"))
        self.assertIsNone(decided_block(lines, 10, "other"))
        shifted = NOTEBOOK.replace("-- @decide bound : some goal\n", "-- @decide bound : x\n\n")
        self.assertEqual(decided_block(shifted.split("\n"), 2, "bound"), (3, 9))

    def test_rejects_other_content_before_the_generated_block(self) -> None:
        """Only blank lines may separate a directive from its generated block."""
        shifted = NOTEBOOK.replace(
            "-- @decide bound : some goal\n", "-- @decide bound : x\n#check True\n"
        )
        self.assertIsNone(decided_block(shifted.split("\n"), 2, "bound"))

    def test_finds_a_block_after_an_older_shared_prelude(self) -> None:
        """A legacy shared definition block does not hide the decision block."""
        shared = "namespace DecidedShared_abc\n\ndef x := 1\n\nend DecidedShared_abc\n\n"
        shifted = NOTEBOOK.replace(BLOCK, shared + BLOCK)
        self.assertEqual(decided_block(shifted.split("\n"), 2, "bound"), (8, 14))

    def test_an_unclosed_block_is_not_replaced(self) -> None:
        """A namespace whose end is missing before the next directive is kept."""
        text = NOTEBOOK.replace("end Decided_bound", "end Other")
        self.assertIsNone(decided_block(text.split("\n"), 2, "bound"))

    def test_reinserting_the_block_restores_the_source(self) -> None:
        """Removing the block and inserting it as Accept does is the identity."""
        span = decided_block(NOTEBOOK.split("\n"), 2, "bound")
        assert span is not None
        removed = without_lines(NOTEBOOK, span)
        self.assertNotIn("Decided_bound", removed)
        self.assertEqual(with_block(removed, 2, BLOCK), NOTEBOOK)


class RerunTests(unittest.TestCase):
    """Choose the decisions and evidence whose saved runs are out of date."""

    def test_reruns_stale_cards_only(self) -> None:
        """Current, accepted and never-run cards are left alone."""
        cards = [
            {"key": "a", "status": "stale"},
            {"key": "b", "status": "current"},
            {"key": "c", "status": "never"},
        ]
        self.assertEqual(to_rerun(cards), ["a"])

    def test_replaces_a_decision_whose_block_changed(self) -> None:
        """A decision followed by an earlier block is rerun unless accepted."""
        lines = NOTEBOOK.split("\n")
        card = {"key": "k", "end_line": 2, "name": "bound"}
        self.assertEqual(to_rerun([{**card, "status": "candidate"}], lines), ["k"])
        self.assertEqual(to_rerun([{**card, "status": "accepted"}], lines), [])
        other = {"key": "o", "end_line": 10, "name": "other", "status": "unknown"}
        self.assertEqual(to_rerun([other], lines), [])

    def test_forces_named_decisions_even_when_never_run_or_accepted(self) -> None:
        """A release can refresh exact named receipts without running every card."""
        cards = [
            {"key": "a", "end_line": 2, "name": "proved", "status": "accepted"},
            {"key": "b", "end_line": 3, "name": "unknown", "status": "never"},
            {"key": "c", "end_line": 4, "name": "other", "status": "accepted"},
        ]
        self.assertEqual(
            to_rerun(cards, NOTEBOOK.split("\n"), {"proved", "unknown"}),
            ["a", "b"],
        )

    def test_busy_names_only_the_lean_slot(self) -> None:
        """Only Glitnir's busy-slot refusal is retried."""
        self.assertTrue(busy("Another Lean run is in progress; retry when it finishes."))
        self.assertFalse(busy("Project check timed out."))
        self.assertFalse(busy(None))


class EnvironmentTests(unittest.TestCase):
    """Decide accepted decisions saved in another environment again."""

    def records(self, *fingerprints: str) -> dict:
        """Return results in environment "now" with one decision per fingerprint."""
        return {
            "environment": {"fingerprint": "now", "check": "c"},
            "decisions": {
                f"k{index}": {"fingerprint": fingerprint}
                for index, fingerprint in enumerate(fingerprints)
            },
        }

    def test_finds_decisions_saved_in_another_environment(self) -> None:
        """Only decisions whose fingerprint differs from the check's are returned."""
        self.assertEqual(other_environment(self.records("now", "old", "older")), {"k1", "k2"})
        self.assertEqual(other_environment(self.records("now")), set())

    def test_without_a_recorded_environment_nothing_is_outdated(self) -> None:
        """Results that were never checked give no environment to compare with."""
        self.assertEqual(other_environment(None), set())
        self.assertEqual(other_environment({"decisions": {"k": {"fingerprint": "x"}}}), set())

    def run_refresh(self, records: dict, refreshes: bool) -> tuple[Recheck, list, dict]:
        """Drive `refresh_environment` with a fake service; return what it did."""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Example.lean"
            path.write_text("-- @decide bound : goal\n")
            results = path.with_suffix(".glitnir.json")
            results.write_text(json.dumps(records))
            checker = Recheck.__new__(Recheck)
            checker.path, checker.problems, checker.done = path, [], []
            cards = [
                {"key": key, "name": f"name_{key}"} for key in records["decisions"]
            ]
            checker.service = SimpleNamespace(snapshot=lambda: {"decisions": cards})
            decided: list = []

            def decide(only: set[str] | None = None) -> None:
                """Record the keys asked for and, if wanted, save them as current."""
                decided.append(only)
                if refreshes:
                    for key in only or ():
                        records["decisions"][key]["fingerprint"] = "now"
                    results.write_text(json.dumps(records))

            checks: list = []
            checker.decide = decide  # type: ignore[method-assign]
            checker.check = lambda: checks.append(1) or {"status": "checked_snapshot"}  # type: ignore[method-assign]
            state = checker.refresh_environment({"status": "checked_snapshot", "first": True})
            return checker, decided, {"checks": len(checks), "state": state}

    def test_current_decisions_cost_nothing(self) -> None:
        """No decision is run and the notebook is not checked again."""
        checker, decided, result = self.run_refresh(self.records("now"), refreshes=True)
        self.assertEqual(decided, [])
        self.assertEqual(result["checks"], 0)
        self.assertTrue(result["state"]["first"])
        self.assertEqual(checker.problems, [])

    def test_outdated_decisions_are_decided_and_checked_again(self) -> None:
        """Exactly the outdated decisions run, then the notebook is checked again."""
        checker, decided, result = self.run_refresh(
            self.records("now", "old"), refreshes=True
        )
        self.assertEqual(decided, [{"k1"}])
        self.assertEqual(result["checks"], 1)
        self.assertNotIn("first", result["state"])
        self.assertEqual(checker.problems, [])

    def test_a_record_without_its_directive_is_left_alone(self) -> None:
        """A saved decision whose directive is gone cannot be decided again."""
        records = self.records("now", "old")
        checker = Recheck.__new__(Recheck)
        checker.problems = []
        with tempfile.TemporaryDirectory() as directory:
            checker.path = Path(directory) / "Example.lean"
            checker.path.with_suffix(".glitnir.json").write_text(json.dumps(records))
            checker.service = SimpleNamespace(
                snapshot=lambda: {"decisions": [{"key": "k0", "name": "kept"}]}
            )
            state = {"status": "checked_snapshot"}
            self.assertIs(checker.refresh_environment(state), state)
        self.assertEqual(checker.problems, [])

    def test_a_decision_left_in_another_environment_is_a_problem(self) -> None:
        """A refresh that does not land is reported by the decision's name."""
        checker, _, _ = self.run_refresh(self.records("now", "old"), refreshes=False)
        self.assertEqual(
            checker.problems, ["decision name_k1 is still saved in another environment"]
        )


class SummaryTests(unittest.TestCase):
    """Summarize saved results before and after a recheck."""

    def test_counts_claims_by_status(self) -> None:
        """Counts are sorted by status; missing results count nothing."""
        records = {"claims": [claim("a", "checked"), claim("b", "admitted"), claim("c", "checked")]}
        self.assertEqual(claim_counts(records), {"admitted": 1, "checked": 2})
        self.assertEqual(claim_counts(None), {})

    def test_reports_where_claims_are_withheld(self) -> None:
        """A withheld check names its first unchecked line."""
        self.assertEqual(withheld_from({"withheld": {"from_line": 12, "message": "x"}}), 12)
        self.assertIsNone(withheld_from({"withheld": None}))

    def test_lists_every_changed_status(self) -> None:
        """Changed, added and removed claims are listed by name."""
        before = {"claims": [claim("a", "checked"), claim("b", "admitted"), claim("c", "checked")]}
        after = {"claims": [claim("a", "checked"), claim("b", "checked"), claim("d", "checked")]}
        self.assertEqual(
            status_changes(before, after),
            [
                {"claim": "b", "before": "admitted", "after": "checked"},
                {"claim": "c", "before": "checked", "after": None},
                {"claim": "d", "before": None, "after": "checked"},
            ],
        )

    def test_compares_examples_by_statement(self) -> None:
        """An example renamed by its new position is the same claim."""
        before = {"claims": [claim("ex_1", "checked", example=True, statement="1 = 1")]}
        after = {"claims": [claim("ex_7", "checked", example=True, statement="1 = 1")]}
        self.assertEqual(status_changes(before, after), [])

    def test_renders_one_row_per_notebook(self) -> None:
        """The Markdown table escapes cell separators."""
        entry = {
            "notebook": "Example",
            "before": {"checked": 1},
            "after": {"checked": 2},
            "withheld_from": None,
            "changes": [{"claim": "b", "before": "admitted", "after": "checked"}],
            "runs": [{"kind": "decision", "name": "bound", "result": "accepted again"}],
            "views": {"total": 1, "saved": 1},
            "problems": ["a | b"],
        }
        text = markdown([entry])
        self.assertIn("| Example | 1 checked | 2 checked | b: admitted → checked | 1/1 |", text)
        self.assertIn("a \\| b", text)


if __name__ == "__main__":
    unittest.main()

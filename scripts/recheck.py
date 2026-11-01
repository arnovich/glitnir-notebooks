"""Recheck every notebook with the installed Glitnir and save what it records.

For each configured notebook, in file order, this drives Glitnir's own preview
service (`glitnir.service.preview.SourcePreviewService`) the way the
editor does, so that ``<Notebook>.glitnir.json`` ends up current:

1. Every decision whose saved entry is out of date is decided again. When the
   directive is followed by the block an earlier decision inserted
   (``namespace Decided_<name>`` ... ``end Decided_<name>``), that block is
   taken out while the provider runs. Only its generated theorem is refreshed;
   prose, shared definitions and identity examples stay in place. A changed
   supporting definition refuses replacement. Decisions never accepted get only their
   saved entry refreshed: no new source is added.
2. Every evidence card whose saved run is out of date is run again.
3. The saved notebook is checked; the check saves its claim results.
4. Every ``-- @view`` is drawn; drawings made in a known environment are saved
   in the results, so the gallery shows them without Lean.

A summary per notebook (claim counts and every status change against the
results found before, the decisions and evidence run, the views saved) is
written as ``report.json`` and ``report.md`` to the report directory.

Usage::

    python -m scripts.recheck [--only NAME ...] [--force-decision NAME] [--report DIR] [--no-runs]

Lean, the notebooks' Lake build and the Glitnir backend with the Forseti
provider (and Z3, for decisions) must be installed. Exits 1 when any notebook
could not be checked, withheld claims, or left a decision, evidence card or
view out of date; the report says which.
"""

import argparse
import hashlib
import json
import sys
import time
from collections import Counter
from collections.abc import Callable, Iterable
from copy import deepcopy
from pathlib import Path
from threading import Event
from typing import Any

from scripts.check_bundles import notebook_paths, results_path
from scripts.decision_refresh import PreservationError, refresh_decision, source_lines

#: Seconds between polls of a running check, decision, evidence run or view.
POLL_SECONDS = 15.0
#: Seconds to wait before asking again while another Lean run holds the slot.
BUSY_SECONDS = 60.0
#: How often a request refused for a busy Lean slot is asked again.
BUSY_ATTEMPTS = 120
#: Glitnir's words for a Lean slot held by another process (`SLOT_BUSY`).
_BUSY = ("Another Lean run is in progress",)


def log(message: str) -> None:
    """Print a timestamped progress line."""
    print(f"{time.strftime('%H:%M:%S')} {message}", flush=True)


def busy(message: object) -> bool:
    """Whether ``message`` says another Lean run holds the slot."""
    return isinstance(message, str) and any(word in message for word in _BUSY)


def normal_text(path: Path) -> str:
    """Read a notebook as Glitnir does: UTF-8 with CRLF read as LF."""
    return path.read_bytes().decode("utf-8").replace("\r\n", "\n")


def text_sha256(text: str) -> str:
    """Hash normalized source text as Glitnir does."""
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def read_records(path: Path) -> dict[str, Any] | None:
    """Return a notebook's saved results as JSON, or None when absent."""
    try:
        return json.loads(results_path(path).read_text())
    except (OSError, ValueError):
        return None


def claim_counts(records: dict[str, Any] | None) -> dict[str, int]:
    """Count saved claims by status."""
    counts = Counter(claim["status"] for claim in (records or {}).get("claims", []))
    return dict(sorted(counts.items()))


def withheld_from(records: dict[str, Any] | None) -> int | None:
    """Return the line saved results stop at, or None when nothing is withheld."""
    withheld = (records or {}).get("withheld")
    return withheld.get("from_line") if isinstance(withheld, dict) else None


def status_changes(
    before: dict[str, Any] | None, after: dict[str, Any] | None
) -> list[dict[str, str | None]]:
    """List every claim, by name, whose saved status differs between results.

    A claim present on one side only is listed with None on the other.
    Examples are named by the checker after their position, so they are
    compared by statement text when they have one.
    """

    def by_name(records: dict[str, Any] | None) -> dict[str, str]:
        found = {}
        for claim in (records or {}).get("claims", []):
            name = claim["name"]
            if claim.get("example") and isinstance(claim.get("statement"), str):
                name = f"example: {claim['statement']}"
            found[name] = claim["status"]
        return found

    old, new = by_name(before), by_name(after)
    return [
        {"claim": name, "before": old.get(name), "after": new.get(name)}
        for name in sorted(old.keys() | new.keys())
        if old.get(name) != new.get(name)
    ]


def decided_block(lines: list[str], end_line: int, name: str) -> tuple[int, int] | None:
    """Find the block an earlier decision of ``name`` inserted after its directive.

    Args:
        lines: The notebook's lines.
        end_line: The directive's last line, one-based.
        name: The directive's claim name.

    Returns:
        The block's zero-based start and end (exclusive) line indexes, or None
        when the directive is not followed by such a block. Formatting blank
        lines and an older generated ``DecidedShared_*`` prelude may appear
        between the directive and its decision namespace.
    """
    lines = source_lines("\n".join(lines))
    opening, closing = f"namespace Decided_{name}", f"end Decided_{name}"
    start = end_line
    while start < len(lines) and not lines[start].strip():
        start += 1
    if start < len(lines) and lines[start].startswith("namespace DecidedShared_"):
        shared_close = f"end {lines[start].removeprefix('namespace ')}"
        for index in range(start + 1, len(lines)):
            if lines[index] == shared_close:
                start = index + 1
                while start < len(lines) and not lines[start].strip():
                    start += 1
                break
            if lines[index].startswith("-- @decide "):
                return None
        else:
            return None
    if start >= len(lines) or lines[start] != opening:
        return None
    for index in range(start + 1, len(lines)):
        if lines[index] == closing:
            return start, index + 1
        if lines[index].startswith("-- @decide "):
            break
    return None


def without_lines(text: str, span: tuple[int, int]) -> str:
    """Return ``text`` without the lines in ``span`` (zero-based, end exclusive)."""
    lines = text.split("\n")
    return "\n".join(lines[: span[0]] + lines[span[1] :])


def with_block(text: str, after_line: int, block: str) -> str:
    """Insert ``block`` after the one-based ``after_line``, as Accept does."""
    lines = text.split("\n")
    return "\n".join(lines[:after_line] + block.split("\n") + lines[after_line:])


def to_rerun(
    cards: Iterable[dict[str, Any]],
    lines: list[str] | None = None,
    forced: set[str] | None = None,
) -> list[str]:
    """Return the keys of the cards to run again, in file order.

    A card is run again when its saved run is out of date (``stale``). With
    ``lines``, the cards are decisions, and a decision that is not accepted
    but is followed by an earlier decision's block is run again too, so that
    its block is replaced.
    """
    forced = forced or set()
    keys = []
    for card in cards:
        replace = (
            lines is not None
            and card.get("status") != "accepted"
            and decided_block(lines, card["end_line"], card["name"]) is not None
        )
        if card.get("status") == "stale" or replace or card.get("name") in forced:
            keys.append(card["key"])
    return keys


def markdown(report: list[dict[str, Any]]) -> str:
    """Render the per-notebook summary as a Markdown table and notes."""

    def counts(value: dict[str, int]) -> str:
        return ", ".join(f"{count} {status}" for status, count in value.items()) or "-"

    def cell(text: str) -> str:
        return text.replace("|", "\\|").replace("\n", " ")

    rows = [
        "| Notebook | Before | After | Status changes | Views saved | Runs | Problems |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for entry in report:
        changes = "; ".join(
            f"{c['claim']}: {c['before']} → {c['after']}" for c in entry["changes"]
        )
        views = entry["views"]
        runs = "; ".join(f"{r['kind']} {r['name']}: {r['result']}" for r in entry["runs"])
        withheld = entry.get("withheld_from")
        after = counts(entry["after"]) + (
            f", withheld from line {withheld}" if withheld else ""
        )
        rows.append(
            f"| {entry['notebook']} | {counts(entry['before'])} | {after} | "
            f"{cell(changes or 'none')} | {views['saved']}/{views['total']} | "
            f"{cell(runs or '-')} | {cell('; '.join(entry['problems']) or 'none')} |"
        )
    return "# Notebook recheck\n\n" + "\n".join(rows) + "\n"


class Recheck:
    """Recheck one notebook through Glitnir's preview service."""

    def __init__(
        self,
        path: Path,
        *,
        runs: bool = True,
        force_decisions: set[str] | None = None,
    ) -> None:
        """Prepare the service for ``path``; nothing runs until `run`."""
        from glitnir.service.preview import SourcePreviewService

        self.path = path
        self.runs = runs
        self.force_decisions = force_decisions or set()
        self.service = SourcePreviewService(path)
        self.problems: list[str] = []
        self.done: list[dict[str, str]] = []

    def _retrying(self, start: Callable[[], Any]) -> Any:
        """Call ``start`` again while it is refused because Lean is busy."""
        for _ in range(BUSY_ATTEMPTS):
            try:
                return start()
            except ValueError as error:  # Glitnir's refusals are ValueErrors
                if not busy(str(error)):
                    raise
            log("Lean is busy elsewhere; asking again shortly")
            time.sleep(BUSY_SECONDS)
        raise RuntimeError("Lean stayed busy")

    def _card(self, section: str, key: str) -> dict[str, Any]:
        return next(c for c in self.service.snapshot()[section] if c["key"] == key)

    def _wait_run(self, section: str, key: str) -> dict[str, Any]:
        while (card := self._card(section, key))["status"] == "running":
            time.sleep(POLL_SECONDS)
        return card

    def _run_card(self, section: str, card: dict[str, Any]) -> dict[str, Any]:
        """Run one decision or evidence card until it is no longer busy."""
        for _ in range(BUSY_ATTEMPTS):
            sha = text_sha256(normal_text(self.path))
            if section == "decisions":
                start = self.service.run_decision
            else:
                start = self.service.run_evidence
            key = self._retrying(lambda: start(sha, card["line"]))
            finished = self._wait_run(section, key)
            if not busy(finished.get("run_error")):
                return finished
            time.sleep(BUSY_SECONDS)
        raise RuntimeError("Lean stayed busy")

    def decide(self) -> None:
        """Decide every out-of-date decision again, replacing accepted blocks."""
        lines = normal_text(self.path).split("\n")
        for key in to_rerun(
            self.service.snapshot()["decisions"], lines, self.force_decisions
        ):
            card = self._card("decisions", key)
            original = normal_text(self.path)
            previous_entry = deepcopy(
                (read_records(self.path) or {}).get("decisions", {}).get(key)
            )
            owned_entry = None
            span = decided_block(original.split("\n"), card["end_line"], card["name"])
            temporary = without_lines(original, span) if span is not None else original
            if span is not None:
                self.path.write_text(temporary, encoding="utf-8")
            accepted = False
            owned_text = temporary
            try:
                finished = self._run_card("decisions", card)
                result = finished["status"]
                if finished.get("run_error"):
                    result = f"failed: {finished['run_error']}"
                elif span is not None and finished["status"] == "candidate":
                    candidate = self.service.decision_candidate(key)
                    text = normal_text(self.path)
                    if text != temporary or candidate["sha256"] != text_sha256(text):
                        raise RuntimeError("the notebook changed during the decision")
                    entry = (read_records(self.path) or {}).get("decisions", {}).get(key)
                    if (
                        entry is None or entry["outcome"]["block"] != candidate["block"]
                        or entry["outcome"] != finished.get("outcome")
                        or entry.get("verification") != finished.get("verification")
                    ):
                        raise PreservationError("The saved decision changed during refresh.")
                    owned_entry = deepcopy(entry)
                    refreshed = refresh_decision(original, card["name"], candidate["block"])
                    # Include the original whitespace and any shared prelude
                    # between the directive and the decision namespace. This
                    # exact block must both check and follow the directive.
                    tail_lines = len(original.split("\n")) - span[1]
                    end = len(refreshed.split("\n")) - tail_lines
                    block = "\n".join(refreshed.split("\n")[card["end_line"]:end])
                    verification = self._check_refresh(
                        text_sha256(temporary), card["end_line"], block,
                        entry["outcome"]["theorem"],
                    )
                    if normal_text(self.path) != temporary:
                        raise RuntimeError("the notebook changed during verification")
                    self.path.write_text(refreshed, encoding="utf-8")
                    owned_text = refreshed
                    self._save_refresh(key, entry, block, verification)
                    accepted = True
                    result = "accepted again"
            except PreservationError as error:
                result = f"preservation refused: {error}"
            finally:
                if span is not None and not accepted:
                    if normal_text(self.path) == owned_text:
                        self.path.write_text(original, encoding="utf-8")
                    elif normal_text(self.path) != original:
                        self.problems.append(
                            f"decision {card['name']}: source changed externally; not overwritten"
                        )
                    if owned_entry is not None and normal_text(self.path) == original:
                        try:
                            self._restore_refresh(key, previous_entry, owned_entry)
                        except (ValueError, OSError) as error:
                            self.problems.append(
                                f"decision {card['name']}: receipt rollback refused: {error}"
                            )
            log(f"decision {card['name']}: {result}")
            self.done.append({"kind": "decision", "name": card["name"], "result": result})
            if span is not None and not accepted:
                self.problems.append(f"decision {card['name']} kept its old block: {result}")
            elif result.startswith("failed"):
                self.problems.append(f"decision {card['name']} {result}")

    def _check_refresh(
        self, sha256: str, end_line: int, block: str, theorem: str
    ) -> dict[str, Any]:
        """Kernel-check the exact preserved block through Glitnir's checker."""
        from glitnir.lean.project_checking import check_candidate

        verdict = self._retrying(lambda: check_candidate(
            self.path, expected_sha256=sha256, insert_after_line=end_line,
            block=block, theorem=theorem, cancel=Event(),
        ))
        if verdict["status"] != "checked":
            raise PreservationError(f"Preserved block did not check: {verdict['message']}")
        return verdict

    def _save_refresh(
        self, key: str, previous: dict[str, Any], block: str, verification: dict[str, Any]
    ) -> None:
        """Save the checked preserved receipt through Glitnir's records API."""
        from glitnir.notebook.check_records import (
            load_records, save_records, saved_decisions, with_decision,
        )

        records = load_records(self.path)
        decisions = saved_decisions(records)
        if decisions.get(key) != previous:
            raise PreservationError("The saved decision changed during verification.")
        entry = deepcopy(previous)
        entry["outcome"]["block"] = block
        entry["verification"] = verification
        save_records(self.path, with_decision(
            records, key, entry, keep=decisions, notebook=self.path,
        ))

    def _restore_refresh(
        self, key: str, previous: dict[str, Any] | None, owned: dict[str, Any]
    ) -> None:
        """Restore only this run's receipt, retaining unrelated/external changes."""
        from glitnir.notebook.check_records import (
            load_records, save_records, saved_decisions, with_decision, without_decision,
        )

        records = load_records(self.path)
        decisions = saved_decisions(records)
        if decisions.get(key) != owned:
            raise PreservationError("The saved decision changed externally; not overwritten.")
        if previous == owned:
            return
        restored = (
            with_decision(records, key, previous, keep=decisions, notebook=self.path)
            if previous is not None else without_decision(records, key, notebook=self.path)
        )
        save_records(self.path, restored)

    def evidence(self) -> None:
        """Run every out-of-date evidence card again."""
        for key in to_rerun(self.service.snapshot()["evidence"]):
            card = self._card("evidence", key)
            finished = self._run_card("evidence", card)
            name = f"line {card['line']} {card.get('verb', '')}".strip()
            result = finished["status"]
            if finished.get("run_error"):
                result = f"failed: {finished['run_error']}"
                self.problems.append(f"evidence {name} {result}")
            log(f"evidence {name}: {result}")
            self.done.append({"kind": "evidence", "name": name, "result": result})

    def check(self) -> dict[str, Any]:
        """Check the saved notebook and wait for the result Glitnir saves."""
        for _ in range(BUSY_ATTEMPTS):
            sha = text_sha256(normal_text(self.path))
            self._retrying(lambda: self.service.check(sha))
            message = None
            while True:
                state = self.service.snapshot()["preview"]["check"] or {}
                if state.get("message") != message:
                    message = state.get("message")
                    log(f"check: {state.get('status')}: {message}")
                if state.get("status") != "running":
                    break
                time.sleep(POLL_SECONDS)
            if state.get("status") == "checked_snapshot" or not busy(message):
                break
            time.sleep(BUSY_SECONDS)
        if state.get("status") != "checked_snapshot":
            self.problems.append(f"not checked: {state.get('message')}")
        elif state.get("withheld"):
            self.problems.append(
                f"claims withheld from line {state['withheld'].get('from_line')}"
            )
        return state

    def views(self) -> dict[str, int]:
        """Draw every view directive; count those whose drawing was saved."""
        from glitnir.notebook.check_records import load_records, saved_views

        listed = self.service.snapshot()["views"]
        for view in listed:
            where = f"view at line {view['line']}"
            for _ in range(BUSY_ATTEMPTS):
                answer = self.service.view(view["cell"], view["line"])
                while answer.get("status") in ("drawing", "queued"):
                    time.sleep(POLL_SECONDS)
                    answer = self.service.view_job(answer["job"])
                    if answer.get("transient"):
                        answer = self.service.view(view["cell"], view["line"])
                if not busy(answer.get("error")):
                    break
                time.sleep(BUSY_SECONDS)
            if answer.get("error"):
                self.problems.append(f"{where}: {answer['error']}")
            elif answer.get("uncertain"):
                self.problems.append(f"{where}: drawn while the environment was unknown")
            log(f"{where}: {'error' if answer.get('error') else 'drawn'}")
        saved = len(saved_views(load_records(self.path)))
        if saved < len(listed):
            self.problems.append(f"{len(listed) - saved} of {len(listed)} views not saved")
        return {"total": len(listed), "saved": saved}

    def run(self) -> dict[str, Any]:
        """Recheck the notebook; return its summary."""
        before = read_records(self.path)
        state: dict[str, Any] = {}
        views = {"total": 0, "saved": 0}
        try:
            if self.runs:
                self.decide()
                self.evidence()
            state = self.check()
            if state.get("status") == "checked_snapshot":
                views = self.views()
        except Exception as error:  # noqa: BLE001 - reported per notebook
            self.problems.append(f"{type(error).__name__}: {error}")
        finally:
            self.service.close()
        after = read_records(self.path)
        return {
            "notebook": self.path.stem,
            "check": state.get("status"),
            "before": claim_counts(before),
            "after": claim_counts(after),
            "withheld_from": withheld_from(after),
            "changes": status_changes(before, after),
            "runs": self.done,
            "views": views,
            "problems": self.problems,
        }


def main(argv: list[str] | None = None) -> int:
    """Recheck the configured notebooks and write the report."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--only", nargs="+", metavar="NAME", help="notebook names")
    parser.add_argument(
        "--force-decision",
        action="append",
        default=[],
        metavar="NAME",
        help="rerun a named decision even when its saved result is current or absent",
    )
    parser.add_argument("--report", type=Path, default=Path("recheck-report"))
    parser.add_argument(
        "--no-runs",
        action="store_true",
        help="leave decisions and evidence as saved; only check and draw",
    )
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parents[1]
    notebooks = notebook_paths(root)
    if args.only:
        unknown = set(args.only) - {path.stem for path in notebooks}
        if unknown:
            parser.error(f"unknown notebooks: {', '.join(sorted(unknown))}")
        notebooks = [path for path in notebooks if path.stem in args.only]
    args.report.mkdir(parents=True, exist_ok=True)
    report: list[dict[str, Any]] = []
    for path in notebooks:
        log(f"recheck {path.relative_to(root)}")
        report.append(
            Recheck(
                path,
                runs=not args.no_runs,
                force_decisions=set(args.force_decision),
            ).run()
        )
        # Written after every notebook, so a run cut short keeps what it did.
        (args.report / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        (args.report / "report.md").write_text(markdown(report))
        log(f"{path.stem}: {report[-1]['after']} problems={report[-1]['problems']}")
    return 1 if any(entry["problems"] for entry in report) else 0


if __name__ == "__main__":
    sys.exit(main())

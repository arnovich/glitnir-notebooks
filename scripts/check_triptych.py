"""Validate the exact proof/refutation/unknown release matrix.

The saved Glitnir decision is only one part of a publication receipt. This
guard joins it to the directive text, source and result files, environment,
Lean toolchain and Lake dependency pins recorded in a release manifest.
"""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any


FORMAT = "glitnir.triptych-release/v1"
GLITNIR_TAG = "v0.1.12"
SHA256 = re.compile(r"[0-9a-f]{64}")
DECISION_LIMITS = {
    "wall_time_ms": 300_000,
    "max_variables": 8,
    "max_nodes": 512,
    "max_depth": 64,
    "max_degree": 8,
    "max_monomials": 4_096,
    "max_dictionary": 16,
    "max_weights": 512,
    "max_coefficient_bits": 256,
    "max_artifact_bytes": 1_048_576,
    "max_lean_output_bytes": 1_048_576,
    "max_heartbeats": 2_000_000,
}


class ReleaseError(ValueError):
    """The triptych release manifest does not match its checked artifacts."""


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _source_sha(path: Path) -> str:
    text = path.read_bytes().decode("utf-8").replace("\r\n", "\n")
    return _sha(text.encode("utf-8"))


def _read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text())
    except (OSError, ValueError, RecursionError) as error:
        raise ReleaseError(f"{path}: cannot read JSON: {error}") from None
    if not isinstance(value, dict):
        raise ReleaseError(f"{path}: expected a JSON object")
    return value


def _decision_key(directive: str) -> str:
    """Return Glitnir's key for a unique, single-line decision directive."""
    return _sha(f"{directive.rstrip()}\n0".encode("utf-8"))


def _prefix_sha(source: str, directive: str) -> str:
    """Return Glitnir's source-prefix hash through ``directive``."""
    lines = source.split("\n")
    matches = [index for index, line in enumerate(lines) if line.rstrip() == directive]
    if len(matches) != 1:
        raise ReleaseError(
            f"cannot identify one exact directive for prefix: {directive}"
        )
    return _sha("\n".join(lines[: matches[0] + 1]).encode("utf-8"))


def _package_pins(root: Path) -> dict[str, str]:
    manifest = _read_json(root / "lake-manifest.json")
    pins = {}
    for package in manifest.get("packages", []):
        if isinstance(package, dict) and isinstance(package.get("name"), str):
            pins[package["name"]] = package.get("rev")
    return pins


def _check_decision(
    notebook: str,
    source: str,
    records: dict[str, Any],
    expected: dict[str, Any],
) -> None:
    name = expected.get("name")
    directive = expected.get("directive")
    outcome = expected.get("outcome")
    if not all(isinstance(value, str) for value in (name, directive, outcome)):
        raise ReleaseError(f"{notebook}: malformed expected decision")
    matching = [
        line.rstrip()
        for line in source.splitlines()
        if line.rstrip().startswith(f"-- @decide {name} :")
    ]
    if matching != [directive]:
        raise ReleaseError(
            f"{notebook}/{name}: directive differs or is not unique: {matching!r}"
        )
    entry = records.get("decisions", {}).get(_decision_key(directive))
    if not isinstance(entry, dict):
        raise ReleaseError(f"{notebook}/{name}: no saved decision receipt")
    if entry.get("provider") != "forseti":
        raise ReleaseError(f"{notebook}/{name}: decision provider is not forseti")
    if entry.get("fingerprint") != records["environment"]["fingerprint"]:
        raise ReleaseError(f"{notebook}/{name}: decision environment differs")
    found = entry.get("outcome")
    if not isinstance(found, dict) or found.get("status") != outcome:
        raise ReleaseError(
            f"{notebook}/{name}: expected {outcome}, found "
            f"{found.get('status') if isinstance(found, dict) else None}"
        )
    if not isinstance(found.get("reason"), str) or not found["reason"]:
        raise ReleaseError(f"{notebook}/{name}: decision has no reason")
    if not isinstance(found.get("stages"), list) or not found["stages"]:
        raise ReleaseError(f"{notebook}/{name}: decision has no bounded-run stages")

    verification = entry.get("verification")
    expected_axioms = expected.get("axioms")
    if outcome == "unknown":
        if (
            verification is not None
            or found.get("block") is not None
            or found.get("theorem") is not None
        ):
            raise ReleaseError(
                f"{notebook}/{name}: UNKNOWN must have no theorem or verification"
            )
        if (
            expected.get("verification_type_sha256") is not None
            or expected_axioms != []
        ):
            raise ReleaseError(f"{notebook}/{name}: malformed UNKNOWN expectation")
        if found.get("reason") != "exhausted":
            raise ReleaseError(f"{notebook}/{name}: UNKNOWN run was not exhausted")
        expected_lanes = [
            ("binding", "supported"),
            ("certificate", "none"),
            ("initial-witness", "none"),
        ]
        stages = found.get("stages")
        if len(stages) != len(expected_lanes) or any(
            not isinstance(stage, list)
            or len(stage) != 3
            or tuple(stage[:2]) != lane
            or not isinstance(stage[2], str)
            or not stage[2]
            for stage, lane in zip(stages, expected_lanes)
        ):
            raise ReleaseError(f"{notebook}/{name}: UNKNOWN bounded-run lanes differ")
        if entry.get("prefix_sha256") != _prefix_sha(source, directive):
            raise ReleaseError(f"{notebook}/{name}: UNKNOWN source prefix is stale")
        if re.search(rf"(?m)^namespace\s+Decided_{re.escape(name)}\s*$", source):
            raise ReleaseError(
                f"{notebook}/{name}: UNKNOWN retains a generated theorem namespace"
            )
        return

    if not isinstance(verification, dict) or verification.get("status") != "checked":
        raise ReleaseError(f"{notebook}/{name}: theorem or negation was not checked")
    axioms = verification.get("axioms")
    if axioms != expected_axioms:
        raise ReleaseError(f"{notebook}/{name}: checked axioms differ")
    block = found.get("block")
    theorem = found.get("theorem")
    if not isinstance(block, str) or not isinstance(theorem, str):
        raise ReleaseError(f"{notebook}/{name}: checked outcome has no theorem block")
    if (
        source.count(block) != 1
        or re.search(
            rf"(?m)^{re.escape(directive)}\n(?:[ \t]*\n)*{re.escape(block)}(?:\n|$)",
            source,
        )
        is None
    ):
        raise ReleaseError(
            f"{notebook}/{name}: checked theorem block is not present exactly once after its directive"
        )
    if "sorryAx" in axioms or "sorry" in block:
        raise ReleaseError(
            f"{notebook}/{name}: sorryAx is forbidden in a release receipt"
        )
    if outcome == "refuted" and theorem != f"{name}_refuted":
        raise ReleaseError(
            f"{notebook}/{name}: refutation theorem is not {name}_refuted"
        )
    checked_type = verification.get("type")
    if not isinstance(checked_type, str) or _sha(checked_type.encode()) != expected.get(
        "verification_type_sha256"
    ):
        raise ReleaseError(f"{notebook}/{name}: checked proposition differs")


def check_release(root: Path, manifest_path: Path) -> int:
    """Validate ``manifest_path`` against ``root`` and return decision count."""
    root = root.resolve()
    manifest = _read_json(manifest_path)
    if manifest.get("format") != FORMAT or manifest.get("glitnir_tag") != GLITNIR_TAG:
        raise ReleaseError(f"expected {FORMAT} pinned to Glitnir {GLITNIR_TAG}")
    if manifest.get("decision_limits") != DECISION_LIMITS:
        raise ReleaseError(f"decision limits differ from Glitnir {GLITNIR_TAG} defaults")
    toolchain = (root / "lean-toolchain").read_text().strip()
    if toolchain != manifest.get("lean_toolchain"):
        raise ReleaseError("Lean toolchain differs from the release manifest")
    lake_manifest = root / "lake-manifest.json"
    if _sha(lake_manifest.read_bytes()) != manifest.get("lake_manifest_sha256"):
        raise ReleaseError(
            "full Lake dependency manifest differs from the release manifest"
        )
    pins = _package_pins(root)
    expected_pins = {name: pins.get(name) for name in ("asgard", "forseti")}
    if manifest.get("lake_pins") != expected_pins or not all(
        isinstance(revision, str) and revision for revision in expected_pins.values()
    ):
        raise ReleaseError("Lake dependency pins differ from the release manifest")

    notebooks = manifest.get("notebooks")
    if not isinstance(notebooks, list) or not notebooks:
        raise ReleaseError("release manifest has no notebooks")
    checked = 0
    for notebook in notebooks:
        if not isinstance(notebook, dict) or not isinstance(
            notebook.get("source"), str
        ):
            raise ReleaseError("malformed notebook entry")
        relative = Path(notebook["source"])
        source_path = (root / relative).resolve()
        if (
            relative.is_absolute()
            or not source_path.is_relative_to(root)
            or not source_path.is_file()
        ):
            raise ReleaseError(f"notebook source escapes the repository: {relative}")
        result_path = source_path.with_suffix(".glitnir.json")
        if _source_sha(source_path) != notebook.get("source_sha256"):
            raise ReleaseError(f"{relative}: source SHA-256 differs")
        if not result_path.is_file() or _sha(result_path.read_bytes()) != notebook.get(
            "results_sha256"
        ):
            raise ReleaseError(f"{relative}: results SHA-256 differs")
        records = _read_json(result_path)
        if records.get("source_sha256") != notebook["source_sha256"]:
            raise ReleaseError(f"{relative}: results name another source")
        if records.get("withheld") is not None:
            raise ReleaseError(f"{relative}: claims are withheld")
        if records.get("environment") != notebook.get("environment"):
            raise ReleaseError(f"{relative}: check environment differs")
        source = source_path.read_text().replace("\r\n", "\n")
        decisions = notebook.get("decisions")
        if not isinstance(decisions, list) or not decisions:
            raise ReleaseError(f"{relative}: release matrix has no decisions")
        for decision in decisions:
            if not isinstance(decision, dict):
                raise ReleaseError(f"{relative}: malformed decision expectation")
            _check_decision(str(relative), source, records, decision)
            checked += 1
    return checked


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("manifest", type=Path)
    parser.add_argument(
        "--root", type=Path, default=Path(__file__).resolve().parents[1]
    )
    args = parser.parse_args(argv)
    try:
        count = check_release(args.root, args.manifest)
    except (OSError, ReleaseError) as error:
        print(f"Triptych release invalid: {error}", file=sys.stderr)
        return 1
    print(f"Triptych release: {count} saved decisions match their exact receipts.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

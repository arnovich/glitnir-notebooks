"""Release-matrix guards for the proved/refuted/unresolved triptych."""

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts.check_triptych import ReleaseError, check_release


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class TriptychReleaseTests(unittest.TestCase):
    """A composite receipt binds directives, decisions, sources and all pins."""

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        (self.root / "examples/dynamics").mkdir(parents=True)
        self.source = self.root / "examples/dynamics/Demo.lean"
        self.directives = [
            "-- @decide proved : trajectory demo observe V always : V <= 2",
            "-- @decide refuted : trajectory demo observe V always : V <= 0",
            "-- @decide unresolved : trajectory demo observe V always : V <= 1",
        ]
        self.blocks = [
            "theorem proved : True := by trivial",
            "theorem refuted_refuted : True := by trivial",
        ]
        text = (
            f"{self.directives[0]}\n\n{self.blocks[0]}\n\n"
            f"{self.directives[1]}\n\n{self.blocks[1]}\n\n"
            f"{self.directives[2]}\n"
        )
        self.source.write_text(text)
        key = lambda line: _sha(f"{line}\n0".encode())
        checked = {
            "status": "checked",
            "message": "checked",
            "axioms": ["propext"],
            "type": "True",
        }
        decisions = {
            key(self.directives[0]): self._entry(
                "proven", "proved", self.blocks[0], checked
            ),
            key(self.directives[1]): self._entry(
                "refuted",
                "refuted_refuted",
                self.blocks[1],
                {**checked, "type": "Not False"},
            ),
            key(self.directives[2]): self._entry("unknown", None, None, None),
        }
        decisions[key(self.directives[2])]["prefix_sha256"] = self._prefix_sha(
            text, self.directives[2]
        )
        results = {
            "format": "glitnir.project-checks/v2",
            "source_sha256": _sha(text.encode()),
            "environment": {"fingerprint": "f" * 64, "check": "c" * 64},
            "withheld": None,
            "claims": [],
            "decisions": decisions,
        }
        self.result_path = self.source.with_suffix(".glitnir.json")
        self.result_path.write_text(json.dumps(results, sort_keys=True))
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.32.1\n")
        self.lake_manifest = self.root / "lake-manifest.json"
        self.lake_manifest.write_text(
            json.dumps(
                {
                    "packages": [
                        {"name": "forseti", "rev": "a" * 40},
                        {"name": "asgard", "rev": "b" * 40},
                    ]
                }
            )
        )
        self.manifest = self.root / "release.json"
        self.manifest.write_text(
            json.dumps(
                {
                    "format": "glitnir.triptych-release/v1",
                    "glitnir_tag": "v0.1.12",
                    "decision_limits": {
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
                    },
                    "lean_toolchain": "leanprover/lean4:v4.32.1",
                    "lake_manifest_sha256": _sha(self.lake_manifest.read_bytes()),
                    "lake_pins": {"forseti": "a" * 40, "asgard": "b" * 40},
                    "notebooks": [
                        {
                            "source": "examples/dynamics/Demo.lean",
                            "source_sha256": _sha(text.encode()),
                            "results_sha256": _sha(self.result_path.read_bytes()),
                            "environment": {
                                "fingerprint": "f" * 64,
                                "check": "c" * 64,
                            },
                            "model": "demo",
                            "observation": "V",
                            "decisions": [
                                self._decision(
                                    "proved", self.directives[0], "proven", "True"
                                ),
                                self._decision(
                                    "refuted",
                                    self.directives[1],
                                    "refuted",
                                    "Not False",
                                ),
                                self._decision(
                                    "unresolved",
                                    self.directives[2],
                                    "unknown",
                                    None,
                                ),
                            ],
                        }
                    ],
                },
                indent=2,
            )
            + "\n"
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    @staticmethod
    def _prefix_sha(text: str, directive: str) -> str:
        line = text.split("\n").index(directive) + 1
        return _sha("\n".join(text.split("\n")[:line]).encode())

    @staticmethod
    def _entry(
        status: str,
        theorem: str | None,
        block: str | None,
        verification: dict | None,
    ) -> dict:
        unknown = status == "unknown"
        return {
            "prefix_sha256": "p" * 64,
            "fingerprint": "f" * 64,
            "provider": "forseti",
            "created": "2026-10-29T08:00:00+00:00",
            "outcome": {
                "status": status,
                "reason": "exhausted" if unknown else "bounded search completed",
                "stages": (
                    [
                        ["binding", "supported", "demo/obs-v"],
                        ["certificate", "none", "bounded certificate lane exhausted"],
                        ["initial-witness", "none", "bounded witness lane exhausted"],
                    ]
                    if unknown
                    else [["lane", status, "exact"]]
                ),
                "block": block,
                "theorem": theorem,
            },
            "verification": verification,
        }

    @staticmethod
    def _decision(
        name: str,
        directive: str,
        outcome: str,
        verification_type: str | None,
    ) -> dict:
        return {
            "name": name,
            "directive": directive,
            "outcome": outcome,
            "verification_type_sha256": (
                _sha(verification_type.encode())
                if verification_type is not None
                else None
            ),
            "axioms": [] if outcome == "unknown" else ["propext"],
        }

    def _write_results(self, results: dict) -> None:
        self.result_path.write_text(json.dumps(results, sort_keys=True))
        manifest = json.loads(self.manifest.read_text())
        manifest["notebooks"][0]["results_sha256"] = _sha(self.result_path.read_bytes())
        self.manifest.write_text(json.dumps(manifest))

    def _write_source(self, text: str, results: dict) -> None:
        self.source.write_text(text)
        results["source_sha256"] = _sha(text.encode())
        self._write_results(results)
        manifest = json.loads(self.manifest.read_text())
        manifest["notebooks"][0]["source_sha256"] = _sha(text.encode())
        self.manifest.write_text(json.dumps(manifest))

    def test_accepts_exact_composite_receipt(self) -> None:
        self.assertEqual(check_release(self.root, self.manifest), 3)

    def test_rejects_missing_unknown_receipt(self) -> None:
        results = json.loads(self.result_path.read_text())
        results["decisions"].pop(next(reversed(results["decisions"])))
        self._write_results(results)
        with self.assertRaisesRegex(ReleaseError, "no saved decision receipt"):
            check_release(self.root, self.manifest)

    def test_rejects_sorry_in_refutation(self) -> None:
        results = json.loads(self.result_path.read_text())
        refuted = next(
            entry
            for entry in results["decisions"].values()
            if entry["outcome"]["status"] == "refuted"
        )
        refuted["verification"]["axioms"].append("sorryAx")
        self._write_results(results)
        manifest = json.loads(self.manifest.read_text())
        manifest["notebooks"][0]["decisions"][1]["axioms"].append("sorryAx")
        self.manifest.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ReleaseError, "sorryAx"):
            check_release(self.root, self.manifest)

    def test_rejects_checked_block_not_immediately_after_directive(self) -> None:
        results = json.loads(self.result_path.read_text())
        text = self.source.read_text().replace(
            f"{self.directives[0]}\n\n{self.blocks[0]}",
            f"{self.directives[0]}\n\n-- moved\n{self.blocks[0]}",
        )
        self._write_source(text, results)
        with self.assertRaisesRegex(ReleaseError, "not present exactly once"):
            check_release(self.root, self.manifest)

    def test_rejects_unknown_without_exact_exhausted_lanes(self) -> None:
        results = json.loads(self.result_path.read_text())
        unknown = next(
            entry
            for entry in results["decisions"].values()
            if entry["outcome"]["status"] == "unknown"
        )
        unknown["outcome"]["stages"][1][1] = "timeout"
        self._write_results(results)
        with self.assertRaisesRegex(ReleaseError, "bounded-run lanes differ"):
            check_release(self.root, self.manifest)

    def test_rejects_unknown_with_stale_prefix(self) -> None:
        results = json.loads(self.result_path.read_text())
        unknown = next(
            entry
            for entry in results["decisions"].values()
            if entry["outcome"]["status"] == "unknown"
        )
        unknown["prefix_sha256"] = "0" * 64
        self._write_results(results)
        with self.assertRaisesRegex(ReleaseError, "source prefix is stale"):
            check_release(self.root, self.manifest)

    def test_rejects_unknown_with_generated_theorem_namespace(self) -> None:
        results = json.loads(self.result_path.read_text())
        text = (
            self.source.read_text()
            + "\nnamespace Decided_unresolved\nend Decided_unresolved\n"
        )
        self._write_source(text, results)
        with self.assertRaisesRegex(ReleaseError, "generated theorem namespace"):
            check_release(self.root, self.manifest)

    def test_rejects_full_lake_dependency_drift(self) -> None:
        lake = json.loads(self.lake_manifest.read_text())
        lake["packages"].append({"name": "mathlib", "rev": "c" * 40})
        self.lake_manifest.write_text(json.dumps(lake))
        with self.assertRaisesRegex(ReleaseError, "full Lake dependency manifest"):
            check_release(self.root, self.manifest)

    def test_rejects_decision_limit_drift(self) -> None:
        manifest = json.loads(self.manifest.read_text())
        manifest["decision_limits"]["wall_time_ms"] = 1
        self.manifest.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ReleaseError, "decision limits differ"):
            check_release(self.root, self.manifest)


if __name__ == "__main__":
    unittest.main()

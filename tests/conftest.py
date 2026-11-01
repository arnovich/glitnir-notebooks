"""Disposable notebook corpus fixtures for the standard-library test suite."""

import hashlib
import json
import subprocess
from pathlib import Path

SOURCE = "theorem example_claim : True := True.intro\n"


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def results_for(text: str) -> dict:
    """Return minimal Glitnir results recorded for the saved source ``text``."""
    return {
        "format": "glitnir.project-checks/v2",
        "source_sha256": _sha(text),
        "environment": {"fingerprint": "f" * 64, "check": "c" * 64},
        "withheld": None,
        "claims": [
            {
                "name": "example_claim",
                "status": "checked",
                "axioms": [],
                "start_line": 1,
                "end_line": 1,
                "declaration_sha256": _sha(text.rstrip("\n")),
                "prefix_sha256": _sha(text.rstrip("\n")),
                "proposition_sha256": "p" * 64,
            }
        ],
    }


def make_corpus(root: Path) -> Path:
    """Create one configured notebook with its saved Glitnir results."""
    directory = root / "examples/basics"
    directory.mkdir(parents=True)
    notebook = directory / "Example.lean"
    notebook.write_text(SOURCE)
    (root / "lakefile.toml").write_text(
        'name = "examples"\ndefaultTargets = ["Example"]\n'
        '[[lean_lib]]\nname = "Example"\nsrcDir = "examples/basics"\n'
    )
    (root / "lake-manifest.json").write_text(
        json.dumps(
            {
                "packagesDir": ".lake/packages",
                "packages": [{"name": "forseti", "type": "git", "rev": "a" * 40}],
            }
        )
    )
    notebook.with_suffix(".glitnir.json").write_text(json.dumps(results_for(SOURCE)))
    return notebook


ORIGINAL_SOURCE = """namespace Proj

/-- Multiplication commutes. -/
theorem mul_comm' : ∀ a b : Nat, a * b = b * a := Nat.mul_comm

end Proj
"""

WALKTHROUGH_SOURCE = """import Main

/-!
# Fixture walkthrough

See [`Main.lean`](https://example.invalid/orig/blob/main/proj/Main.lean).
-/

namespace Fixture

/-- **Theorem 1** -/
theorem theorem1 : ∀ a b : Nat, a * b = b * a := by
  exact Proj.mul_comm'

end Fixture
"""


def git(*args: str) -> str:
    """Run git quietly with a fixed identity and return its output."""
    return subprocess.run(
        ["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid", *args],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def make_original(directory: Path) -> tuple[Path, str]:
    """Create a one-commit repository holding the Lean project ``proj``."""
    (directory / "proj").mkdir(parents=True)
    (directory / "proj/Main.lean").write_text(ORIGINAL_SOURCE)
    git("init", "-q", str(directory))
    git("-C", str(directory), "add", "proj/Main.lean")
    git("-C", str(directory), "commit", "-q", "-m", "original")
    return directory, git("-C", str(directory), "rev-parse", "HEAD")


def outline_for(repository: str, commit: str) -> dict:
    """Return a one-node outline of ``proj`` at ``commit`` in ``repository``."""
    name = repository.rstrip("/").rsplit("/", 1)[-1]
    return {
        "format": "glitnir.walkthrough-outline/v1",
        "title": "Fixture walkthrough",
        "project": {
            "root": f"../_originals/{commit[:12]}/{name}/proj",
            "repository": repository,
            "path": "proj",
            "commit": commit,
            "toolchain": "leanprover/lean4:v4.33.1",
            "trusted": "Main.lean",
        },
        "sources": [{"kind": "paper", "title": "P", "url": "https://example.invalid/p.pdf"}],
        "nodes": [
            {
                "id": "thm1",
                "label": "Theorem 1",
                "kind": "theorem",
                "statement": "$ab = ba$.",
                "idea": "Commutativity.",
                "uses": [],
                "lean": [
                    {
                        "name": "Proj.mul_comm'",
                        "file": "Main.lean",
                        "line": 4,
                        "type": ": ∀ a b : Nat, a * b = b * a",
                    }
                ],
                "claim": "theorem1",
            }
        ],
    }


def make_walkthrough(root: Path, original: Path, commit: str) -> Path:
    """Create ``walkthroughs/fixture`` explaining ``original`` at ``commit``.

    The original is cloned to where ``scripts/fetch_originals.py`` would check
    it out; the outline names it by a public-looking URL, as the published
    maps link to it. Returns the walkthrough's notebook.
    """
    outline = outline_for(f"https://example.invalid/{original.name}", commit)
    folder = root / "walkthroughs/fixture"
    (folder / "assets").mkdir(parents=True)
    (folder / "outline.json").write_text(json.dumps(outline, indent=2) + "\n")
    notebook = folder / "Fixture.lean"
    notebook.write_text(WALKTHROUGH_SOURCE)
    checkout = root / f"walkthroughs/_originals/{commit[:12]}/{original.name}"
    git("clone", "-q", str(original), str(checkout))
    return notebook


def pin_helper(root: Path, helper: Path) -> Path:
    """Pin ``helper`` as the walkthrough helper and place it where it is fetched."""
    commit = "a" * 40
    data = helper.read_bytes()
    (root / "scripts").mkdir(exist_ok=True)
    (root / "scripts/walkthrough-script.txt").write_text(
        f"commit {commit}\nsha256 {hashlib.sha256(data).hexdigest()}\n"
    )
    placed = root / f"walkthroughs/_originals/walkthrough-{commit[:12]}.py"
    placed.parent.mkdir(parents=True, exist_ok=True)
    placed.write_bytes(data)
    return placed


def add_certificate_library(root: Path, default: bool = False) -> Path:
    """Add an opt-in certificate library with a root and one submodule."""
    library = root / "certificates"
    (library / "Certified").mkdir(parents=True)
    (library / "Certified.lean").write_text("import Certified.Main\n")
    (library / "Certified/Main.lean").write_text(SOURCE)
    config = root / "lakefile.toml"
    text = config.read_text()
    if default:
        text = text.replace('defaultTargets = ["Example"]', 'defaultTargets = ["Example", "Certified"]')
    config.write_text(
        text + '[[lean_lib]]\nname = "Certified"\nsrcDir = "certificates"\n'
        'globs = ["Certified.*"]\n'
    )
    return library

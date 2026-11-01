"""Choose which notebooks a pull request needs rechecked.

Reads the changed paths (``git diff --name-only <base>...<head>``) and decides:

* ``all`` when a file that every notebook depends on changed: ``lean-toolchain``,
  ``lake-manifest.json``, ``lakefile.toml``, the gallery or recheck
  requirements, ``scripts/recheck.py``, this script or the workflow, or a
  ``.lean`` file under ``examples/`` that is no configured notebook;
* otherwise the sorted names of the notebooks whose ``.lean`` source changed,
  plus every notebook that imports one of them (transitively);
* an empty list when nothing needs rechecking: results files
  (``*.glitnir.json``), docs and everything else do not.

Usage::

    git diff --name-only BASE...HEAD | python -m scripts.select_recheck

prints ``all``, or the space-separated names (an empty line for none).
Run it from the repository root; it reads ``lakefile.toml`` and the notebooks.
"""

import re
import sys
import tomllib
from collections.abc import Iterable
from pathlib import Path

ALL = "all"

#: Changes that invalidate every notebook's saved results.
EVERYTHING = frozenset(
    {
        "lean-toolchain",
        "lake-manifest.json",
        "lakefile.toml",
        "scripts/gallery/requirements.txt",
        "scripts/glitnir_release.py",
        "scripts/recheck-requirements.txt",
        "scripts/recheck.py",
        "scripts/decision_refresh.py",
        "scripts/decision_source.lark",
        "scripts/select_recheck.py",
        ".github/workflows/recheck.yml",
    }
)

_IMPORT = re.compile(r"^import\s+(.+)$")


def notebook_sources(root: Path) -> dict[str, Path]:
    """Map each configured notebook's name to its source path, relative to ``root``."""
    config = tomllib.loads((root / "lakefile.toml").read_text())
    return {
        library["name"]: Path(library.get("srcDir", ".")) / f"{library['name']}.lean"
        for library in config["lean_lib"]
    }


def imported_modules(text: str) -> set[str]:
    """Return the module names in a notebook's leading ``import`` lines."""
    found: set[str] = set()
    for line in text.split("\n"):
        stripped = line.strip()
        match = _IMPORT.match(stripped)
        if match:
            found.update(match.group(1).split("--")[0].split())
        elif stripped and not stripped.startswith("--"):
            break
    return found


def importers(root: Path, sources: dict[str, Path]) -> dict[str, set[str]]:
    """Map each notebook to the notebooks that import it directly.

    A module ``Name`` or ``Name.Sub`` is the library ``Name``.
    """
    result: dict[str, set[str]] = {name: set() for name in sources}
    for name, source in sources.items():
        path = root / source
        if not path.is_file():
            continue
        for module in imported_modules(path.read_text(encoding="utf-8")):
            library = module.split(".")[0]
            if library in result and library != name:
                result[library].add(name)
    return result


def select_notebooks(changed: Iterable[str], root: Path) -> str | list[str]:
    """Decide what a change set needs rechecked.

    Args:
        changed: Changed paths, relative to the repository root.
        root: The repository root, at the revision to be checked.

    Returns:
        ``"all"``, or the sorted notebook names (empty when none).
    """
    sources = notebook_sources(root)
    by_path = {source.as_posix(): name for name, source in sources.items()}
    selected: set[str] = set()
    for path in changed:
        path = path.strip().removeprefix("./")
        if path in EVERYTHING:
            return ALL
        if path in by_path:
            selected.add(by_path[path])
        elif path.startswith("examples/") and path.endswith(".lean"):
            # A deleted, moved or helper source: no notebook to blame.
            return ALL
    imported_by = importers(root, sources)
    pending = list(selected)
    while pending:
        for dependent in imported_by[pending.pop()] - selected:
            selected.add(dependent)
            pending.append(dependent)
    return sorted(selected)


def main() -> int:
    """Print the selection for the changed paths on standard input."""
    selection = select_notebooks(sys.stdin.read().split("\n"), Path.cwd())
    print(selection if isinstance(selection, str) else " ".join(selection))
    return 0


if __name__ == "__main__":
    sys.exit(main())

"""Validate the Lake notebook inventory, dependency pins and saved Glitnir results.

Every notebook needs a committed ``<Notebook>.glitnir.json`` whose recorded
source SHA-256 is that of the notebook's saved source. The results are read
with Glitnir's own record loader when the Glitnir backend is importable, and
otherwise checked structurally against the same format.

The walkthroughs under ``walkthroughs/`` are not notebooks of this Lake
project: they are never inventoried here, and the Lake configuration may not
name them. ``scripts/check_walkthroughs.py`` checks them.
"""

import argparse
import hashlib
import json
import re
import tempfile
import tomllib
from collections.abc import Iterable
from pathlib import Path
from typing import Any

RESULTS_SUFFIX = ".glitnir.json"
#: Walkthroughs of other Lean projects: never notebooks of this Lake project.
WALKTHROUGHS = "walkthroughs"
_NOT_A_NOTEBOOK = (
    "{} is under walkthroughs/: walkthroughs are not notebooks of the root Lake "
    "project and are checked by scripts/check_walkthroughs.py"
)
FORMATS = ("glitnir.project-checks/v1", "glitnir.project-checks/v2")
MAX_RESULTS_BYTES = 16 * 1024 * 1024
# Opt-in proof libraries, such as AIFSafety: built on request, never notebooks.
CERTIFICATE_DIR = "certificates"
_SHA256 = re.compile(r"[0-9a-f]{64}")
_CLAIM_KEYS: dict[str, type] = {
    "name": str,
    "status": str,
    "axioms": list,
    "start_line": int,
    "end_line": int,
    "declaration_sha256": str,
    "prefix_sha256": str,
    "proposition_sha256": str,
}


class ResultsError(ValueError):
    """A notebook's saved results are missing, malformed or for other source."""


def _file(root: Path, relative: Path) -> Path:
    """Resolve an existing unlinked relative file inside the repository."""
    candidate = root / relative
    target = candidate.resolve()
    if (
        relative.is_absolute()
        or not target.is_relative_to(root)
        or not target.is_file()
    ):
        raise ValueError(f"Missing or escaping file: {relative}")
    if any(
        path.is_symlink()
        for path in (candidate, *candidate.parents)
        if path.is_relative_to(root) and path != root
    ):
        raise ValueError(f"Linked file or directory: {relative}")
    return target


def results_path(notebook: Path) -> Path:
    """Return where Glitnir saves a notebook's check results."""
    return notebook.with_suffix(RESULTS_SUFFIX)


def source_sha256(notebook: Path) -> str:
    """Hash the saved source as Glitnir does: UTF-8 with CRLF read as LF."""
    text = notebook.read_bytes().decode("utf-8").replace("\r\n", "\n")
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _glitnir_loader() -> Any:
    """Return Glitnir's record loader, or None when the backend is not installed."""
    try:
        from glitnir.notebook.check_records import load_records
    except ImportError:
        return None
    return load_records


def validator() -> str:
    """Name how results are validated in this Python environment."""
    return "Glitnir's record loader" if _glitnir_loader() else "structural checks"


def _structural(records: Any) -> str | None:
    """Return why ``records`` is not a Glitnir results file, or None."""
    if not isinstance(records, dict) or records.get("format") not in FORMATS:
        return f"not a Glitnir results file (expected format {FORMATS[-1]})"
    if not isinstance(records.get("source_sha256"), str):
        return "no recorded source SHA-256"
    environment = records.get("environment")
    if not isinstance(environment, dict) or not isinstance(
        environment.get("fingerprint"), str
    ):
        return "no recorded environment fingerprint"
    withheld = records.get("withheld")
    if withheld is not None and not (
        isinstance(withheld, dict)
        and type(withheld.get("from_line")) is int
        and isinstance(withheld.get("message"), str)
    ):
        return "malformed withheld section"
    claims = records.get("claims")
    if not isinstance(claims, list):
        return "no saved claims list"
    for claim in claims:
        if not isinstance(claim, dict) or not all(
            type(claim.get(key)) is kind for key, kind in _CLAIM_KEYS.items()
        ):
            return "malformed saved claim"
    for section in ("evidence", "decisions"):
        if not isinstance(records.get(section, {}), dict):
            return f"malformed {section} section"
    return None


def load_results(path: Path) -> dict[str, Any]:
    """Read one results file, refusing anything Glitnir would not load.

    Raises:
        ResultsError: the file is unreadable, too large or malformed.
    """
    try:
        data = path.read_bytes()
    except OSError as error:
        raise ResultsError(f"cannot be read: {error.strerror}") from None
    if len(data) > MAX_RESULTS_BYTES:
        raise ResultsError("larger than 16 MiB")
    try:
        records = json.loads(data)
    except (ValueError, RecursionError):
        raise ResultsError("not valid JSON") from None
    why = _structural(records)
    if why is not None:
        raise ResultsError(why)
    load_records = _glitnir_loader()
    if load_records is not None:
        # The loader reads only the sidecar of the notebook path it is given.
        with tempfile.TemporaryDirectory(prefix="forseti-results-") as directory:
            copy = Path(directory) / f"Notebook{RESULTS_SUFFIX}"
            copy.write_bytes(data)
            if load_records(Path(directory) / "Notebook.lean") is None:
                raise ResultsError(
                    f"the installed Glitnir backend cannot load these "
                    f"{records['format']} results"
                )
    return records


def check_results(notebook: Path, path: Path | None = None) -> dict[str, Any]:
    """Validate saved results for ``notebook`` and return them.

    Args:
        notebook: The notebook whose saved source the results must match.
        path: The results file; the notebook's own sidecar when None.

    Raises:
        ResultsError: the results are missing, malformed or for other source.
    """
    path = results_path(notebook) if path is None else path
    if path.is_symlink() or not path.is_file():
        raise ResultsError("missing")
    records = load_results(path)
    if records["source_sha256"] != source_sha256(notebook):
        raise ResultsError(
            f"recorded for other source than {notebook.name}; "
            "check the saved notebook again"
        )
    return records


def notebook_paths(directory: Path) -> list[Path]:
    """Validate the Lake inventory and pins; return the configured notebooks."""
    root = directory.resolve()
    config = tomllib.loads((root / "lakefile.toml").read_text())
    for require in config.get("require", []):
        if Path(require.get("path", ".")).parts[:1] == (WALKTHROUGHS,):
            raise ValueError(_NOT_A_NOTEBOOK.format(f"Lake dependency {require.get('name')}"))
    configured = {}
    certificates = set()
    for library in config["lean_lib"]:
        name = library["name"]
        if Path(library.get("srcDir", ".")).parts[:1] == (WALKTHROUGHS,):
            raise ValueError(_NOT_A_NOTEBOOK.format(f"Lake library {name}"))
        if name in configured or name in certificates:
            raise ValueError(f"Duplicate Lake library: {name}")
        source = _file(root, Path(library.get("srcDir", ".")) / f"{name}.lean")
        if library.get("srcDir") == CERTIFICATE_DIR:
            certificates.add(name)
        else:
            configured[name] = source
    if certificates & set(config["defaultTargets"]):
        raise ValueError("Certificate libraries must not be default targets")
    notebooks = [*root.glob("*.lean"), *root.glob("examples/*/*.lean")]
    if (
        not notebooks
        or len(notebooks) != len(configured)
        or {p.resolve() for p in notebooks} != set(configured.values())
        or set(config["defaultTargets"]) != set(configured)
    ):
        raise ValueError("Notebook inventory does not match Lake libraries and targets")
    manifest = json.loads((root / "lake-manifest.json").read_text())
    if manifest["packagesDir"] != ".lake/packages" or not all(
        package["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", package["rev"])
        for package in manifest["packages"]
    ):
        raise ValueError("Dependencies must use portable Git pins")
    return sorted(configured.values())


def check_bundles(
    directory: Path, only: Iterable[str] | None = None
) -> tuple[int, int]:
    """Return notebook and saved-claim counts only if the whole corpus is valid.

    Args:
        directory: The corpus root.
        only: Notebook names whose results are checked; every notebook when None.
            The Lake inventory and pins are always checked in full.

    Raises:
        ValueError: the inventory or pins are invalid, or results are missing
            or invalid; every notebook's problem is named in one message.
    """
    root = directory.resolve()
    paths = notebook_paths(root)
    if only is not None:
        names = set(only)
        unknown = names - {path.stem for path in paths}
        if unknown:
            raise ValueError(f"Unknown notebooks: {', '.join(sorted(unknown))}")
        paths = [path for path in paths if path.stem in names]
    claims = 0
    missing: list[str] = []
    invalid: list[str] = []
    for path in paths:
        relative = results_path(path).relative_to(root).as_posix()
        try:
            _file(root, results_path(path).relative_to(root))
        except ValueError:
            missing.append(relative)
            continue
        try:
            claims += len(check_results(path)["claims"])
        except ResultsError as error:
            invalid.append(f"{relative}: {error}")
    problems = []
    if missing:
        problems.append(
            f"missing Glitnir results for {len(missing)} of {len(paths)} notebooks "
            f"({', '.join(missing)}); check each saved notebook with Glitnir and "
            "commit its <Notebook>.glitnir.json"
        )
    if invalid:
        problems.append("invalid Glitnir results: " + "; ".join(invalid))
    if problems:
        raise ValueError(". ".join(problems))
    return len(paths), claims


def main() -> None:
    """Check a corpus root supplied on the command line or this repository."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "directory", nargs="?", type=Path, default=Path(__file__).resolve().parents[1]
    )
    args = parser.parse_args()
    try:
        notebooks, claims = check_bundles(args.directory)
    except (ValueError, KeyError, OSError) as error:
        parser.exit(1, f"Bundle check failed: {error}\n")
    print(
        f"{notebooks} notebooks with Glitnir results for their saved source "
        f"({claims} saved claims, validated with {validator()}); "
        "all dependency revisions pinned"
    )


if __name__ == "__main__":
    main()

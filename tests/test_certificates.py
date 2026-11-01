"""The AIF notebook must cite the statements its certificate library proves."""

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NOTEBOOK = ROOT / "examples/biochemistry/AntitheticFeedback.lean"
LIBRARY = ROOT / "certificates/AIFSafety/CompleteSafety.lean"
LINK = ROOT / "certificates/AIFSafety/NotebookStatements.lean"
WORKFLOW = ROOT / ".github/workflows/check.yml"

#: Each notebook definition and the library theorem that states it word for word.
CITED = {"ForwardSafety": "forward_safety_statement", "LaterOutput": "later_output_statement"}


def _normalized(text: str) -> str:
    """Collapse whitespace so line breaks and indentation do not count."""
    return " ".join(text.split())


def _definition(source: str, name: str) -> str:
    """The body of `def NAME : Prop :=`, up to the next blank line."""
    match = re.search(rf"(?m)^def {name} : Prop :=\n(.*?)\n\n", source, re.S)
    if match is None:
        raise ValueError(f"no definition {name} in the notebook")
    return _normalized(match[1])


def _statement(source: str, name: str) -> str:
    """The statement of `theorem NAME :`, up to the `:=` before its proof."""
    match = re.search(rf"(?m)^theorem {name} :\n(.*?) :=\n", source, re.S)
    if match is None:
        raise ValueError(f"no theorem {name} in the library")
    return _normalized(match[1])


def _prebuilt_modules() -> set[str]:
    """Modules the check workflow builds one at a time before `lake build`."""
    match = re.search(r"for module in (.*?); do", WORKFLOW.read_text(), re.S)
    if match is None:
        raise ValueError("no prebuild loop in the check workflow")
    modules = set()
    for word in match[1].replace("\\", " ").split():
        expanded = re.fullmatch(r"(.*)\{(\d+)\.\.(\d+)\}", word)
        if expanded:
            first, last = int(expanded[2]), int(expanded[3])
            modules |= {f"{expanded[1]}{n}" for n in range(first, last + 1)}
        else:
            modules.add(word)
    return modules


class CitedStatementTests(unittest.TestCase):
    """The notebook's cited claims and the library's theorems say the same thing."""

    def test_statements_match(self) -> None:
        """Each cited definition's text equals its library theorem's statement.

        Lean checks the correspondence itself in `NotebookStatements`, which CI
        does not build; this comparison is the cheap guard that runs everywhere.
        """
        notebook = NOTEBOOK.read_text()
        library = LIBRARY.read_text()
        for definition, theorem in CITED.items():
            with self.subTest(definition=definition):
                self.assertEqual(
                    _definition(notebook, definition), _statement(library, theorem)
                )

    def test_library_proves_the_notebook_definitions(self) -> None:
        """A library module states each cited definition by its notebook name."""
        link = LINK.read_text()
        self.assertRegex(link, r"(?m)^import AntitheticFeedback$")
        for definition in CITED:
            with self.subTest(definition=definition):
                self.assertRegex(
                    link, rf"(?m)^theorem \w+ : Notebook\.AntitheticFeedback\.{definition} :="
                )


class PrebuildTests(unittest.TestCase):
    """CI builds the notebook's heavy certificate imports one at a time."""

    def test_notebook_certificate_imports_are_prebuilt(self) -> None:
        """Every AIFSafety module the notebook imports is in the prebuild loop."""
        imports = set(re.findall(r"(?m)^import (AIFSafety\.\S+)$", NOTEBOOK.read_text()))
        self.assertTrue(imports)
        self.assertLessEqual(imports, _prebuilt_modules())


if __name__ == "__main__":
    unittest.main()

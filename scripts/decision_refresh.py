"""Refresh a generated theorem without discarding its curated surroundings.

Only the provider's simple, column-zero decision commands are supported.
Definitions must match textually (apart from whitespace and comments), either
locally or in an explicitly opened shared namespace. Ambiguity refuses the edit.
The checked candidate remains the proof source; this module grants no status.
"""

import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from lark import Lark, Token, Tree
from lark.exceptions import LarkError

_LEXER = Lark(
    Path(__file__).with_name("decision_source.lark").read_text(),
    parser="earley",
    propagate_positions=True,
)
_HEAD = re.compile(r"^(namespace|end|open|def|theorem|example)\b(?:\s+([\w'.]+))?")


class PreservationError(ValueError):
    """The candidate cannot safely refresh the retained author-owned context."""


@dataclass(frozen=True)
class _Command:
    """One restricted command and its exact code span, excluding trailing prose."""

    kind: str
    name: str
    start: int
    end: int
    text: str


def _atoms(text: str) -> list[Tree | Token]:
    """Recognize comments and literals before looking for command boundaries."""
    try:
        atoms = _LEXER.parse(text).children
    except LarkError as error:
        raise PreservationError("Cannot identify safe decision-source boundaries.") from error
    for previous, atom in zip(atoms, atoms[1:]):
        if (
            isinstance(previous, Token) and re.search(r"\br#*$", str(previous))
            and isinstance(atom, Tree) and atom.data == "string"
        ):
            raise PreservationError("Raw string syntax is unsupported; keep the old block.")
    return atoms


def _source_masks(text: str) -> tuple[str, str]:
    """Mask literals and comments for boundaries, and only comments for extents."""
    masked, code = list(text), list(text)
    for atom in _atoms(text):
        if isinstance(atom, Token):
            continue
        first, last = atom.meta.start_pos, atom.meta.end_pos
        for index in range(first, last):
            if text[index] != "\n":
                masked[index] = " "
                if atom.data in {"block_comment", "line_comment"}:
                    code[index] = " "
    return "".join(masked), "".join(code)


def source_lines(text: str) -> list[str]:
    """Return code-only lines so prose cannot impersonate namespace markers."""
    return _source_masks(text)[0].split("\n")


def _commands(text: str) -> list[_Command]:
    """Find column-zero commands without reading comment or literal contents."""
    masked_text, code_text = _source_masks(text)
    heads = list(re.finditer(r"^\S[^\n]*", masked_text, re.MULTILINE))
    commands = []
    for index, head in enumerate(heads):
        limit = heads[index + 1].start() if index + 1 < len(heads) else len(text)
        end = head.start() + len(code_text[head.start():limit].rstrip())
        match = _HEAD.match(head.group())
        kind, name = (match[1], match[2] or "") if match else ("unsupported", "")
        commands.append(_Command(kind, name, head.start(), end, text[head.start():end]))
    return commands


def _namespace(commands: list[_Command], name: str) -> list[_Command]:
    """Return exactly one non-nested namespace's commands, refusing ambiguity."""
    starts = [
        i for i, command in enumerate(commands)
        if command.kind == "namespace" and command.name == name
    ]
    if len(starts) != 1:
        raise PreservationError(f"Expected one namespace {name}.")
    start = starts[0]
    for end in range(start + 1, len(commands)):
        command = commands[end]
        if command.kind == "namespace":
            raise PreservationError(f"Nested namespace in {name}; keep the old block.")
        if command.kind == "end":
            if command.name != name:
                break
            return commands[start:end + 1]
    raise PreservationError(f"Cannot find an unambiguous end of {name}.")


def _canonical(text: str) -> tuple[tuple[str, str], ...]:
    """Compare generated code conservatively, preserving literal spelling."""
    pieces = []
    for atom in _atoms(text):
        if isinstance(atom, Token):
            pieces.extend(("code", token) for token in re.findall(r"[\w']+|[^\w\s']+", str(atom)))
        elif atom.data in {"string", "quoted_name"}:
            pieces.append((str(atom.data), text[atom.meta.start_pos:atom.meta.end_pos]))
    return tuple(pieces)


def _definitions(commands: list[_Command]) -> dict[str, _Command]:
    """Index unique definitions; shadowing is not guessed at during refresh."""
    found = {}
    for command in commands:
        if command.kind != "def":
            continue
        if command.name in found:
            raise PreservationError(f"Ambiguous definition {command.name}.")
        found[command.name] = command
    return found


def refresh_decision(original: str, name: str, candidate: str) -> str:
    """Replace only the theorem after proving its retained context unchanged.

    Return the complete notebook, keeping shared preludes, examples, docstrings,
    prose and all text outside the theorem byte-for-byte. Refuse unsupported
    structures, changed definitions or comments inside the replaced proof that
    the fresh candidate would drop. No file is read or written here.
    """
    commands = _commands(original)
    old = _namespace(commands, f"Decided_{name}")[1:-1]
    new_commands = _commands(candidate)
    new = _namespace(new_commands, f"Decided_{name}")[1:-1]
    if len(new_commands) != len(new) + 2:
        raise PreservationError("Candidate contains content outside its decision namespace.")
    if any(c.kind not in {"open", "def", "theorem", "example"} for c in old):
        raise PreservationError("Unsupported author context; keep the old decision block.")
    if any(c.kind not in {"def", "theorem"} for c in new):
        raise PreservationError("Unsupported generated decision context.")
    local = _definitions(old)
    shared: dict[str, _Command] = {}
    for command in old:
        if command.kind != "open":
            continue
        if not re.fullmatch(r"open DecidedShared_[\w]+", command.text):
            raise PreservationError("Unsupported namespace open; keep the old block.")
        definitions = _definitions(_namespace(commands, command.name)[1:-1])
        if shared.keys() & definitions.keys():
            raise PreservationError("Ambiguous shared definitions; keep the old block.")
        shared.update(definitions)
    for definition, generated in _definitions(new).items():
        retained = local.get(definition) or shared.get(definition)
        if retained is None or _canonical(retained.text) != _canonical(generated.text):
            raise PreservationError(f"Supporting definition {definition} changed or is missing.")
    old_theorems = [command for command in old if command.kind == "theorem"]
    new_theorems = [command for command in new if command.kind == "theorem"]
    expected = {name, f"{name}_refuted"}
    if (
        len(old_theorems) != 1 or len(new_theorems) != 1
        or old_theorems[0].name not in expected or new_theorems[0].name not in expected
    ):
        raise PreservationError("Expected one generated decision theorem.")
    before, after = old_theorems[0], new_theorems[0]
    def comments(text: str) -> Counter[str]:
        """Count actual comment atoms, excluding comment-shaped literal text."""
        return Counter(
            text[atom.meta.start_pos:atom.meta.end_pos]
            for atom in _atoms(text)
            if isinstance(atom, Tree) and atom.data in {"block_comment", "line_comment"}
        )

    if not comments(before.text) <= comments(after.text):
        raise PreservationError("Refreshing would drop an authored proof comment.")
    return original[:before.start] + after.text + original[before.end:]

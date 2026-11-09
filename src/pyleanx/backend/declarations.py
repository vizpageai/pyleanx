"""Ask the pinned Lean which declarations exist and what their types are.

Used to validate the curated lemma catalogs (``pyleanx.algebra`` etc.) against the
pinned Mathlib and to index declarations into the theorem bank (M7). This only
*describes* declarations; it never marks anything as verified.
"""

from __future__ import annotations

import shutil
import uuid
from collections.abc import Iterable, Sequence
from dataclasses import dataclass

from ..errors import ProjectError
from ..names import validate_qualified_name
from ..project import LeanProject, find_project
from .subprocess_backend import run_lean


@dataclass(frozen=True)
class DeclInfo:
    name: str
    exists: bool
    type: str | None  # pretty-printed type (pinned toolchain's pretty printer)
    error: str | None = None


def render_check_file(names: Sequence[str], imports: Iterable[str], *,
                      signature: bool = False) -> tuple[str, dict[int, str]]:
    """Lean source with one ``#check @name`` per line, and line -> name.

    With ``signature=True`` it emits ``#check name`` instead, which Lean prints in
    signature form (``name.{u} {α : Type u} [inst] (a b : α) : concl``), as the editor's
    hover/infoview does.
    """
    at = "" if signature else "@"
    mods = sorted(set(imports))
    for m in mods:
        validate_qualified_name(m, "import module")
    lines = [f"import {m}" for m in mods]
    lines += ["", "set_option autoImplicit false", "set_option pp.proofs false"]
    by_line: dict[int, str] = {}
    for n in names:
        validate_qualified_name(n, "declaration name")
        lines.append(f"#check {at}{n}")
        by_line[len(lines)] = n
    return "\n".join(lines) + "\n", by_line


def _strip_head(text: str, name: str) -> str:
    text = text.strip()
    for head in (f"@{name} :", f"{name} :"):
        if text.startswith(head):
            return text[len(head):].strip()
    return text


def check_declarations(
    names: Sequence[str],
    imports: Iterable[str],
    project: LeanProject | str | None = None,
    *,
    timeout: float | None = None,
    signature: bool = False,
) -> dict[str, DeclInfo]:
    """Run ``#check @name`` for every name in one Lean process.

    ``signature=True`` runs ``#check name`` and stores Lean's whole signature line in
    ``DeclInfo.type`` (see :mod:`pyleanx.infoview`).
    """
    proj = find_project(project)
    proj.validate()
    source, by_line = render_check_file(list(dict.fromkeys(names)), imports,
                                        signature=signature)
    work = proj.path / ".pyleanx" / "build" / uuid.uuid4().hex
    work.mkdir(parents=True, exist_ok=True)
    lean_file = work / "PyLeanXDecls.lean"
    lean_file.write_text(source, encoding="utf-8", newline="\n")
    try:
        run = run_lean(proj, lean_file, timeout if timeout is not None else proj.timeout)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    if run.timed_out:
        raise ProjectError("Lean timed out while checking declarations")
    first_decl_line = min(by_line) if by_line else 0
    header_errors = [m.text for m in run.messages
                     if m.severity == "error" and (m.line or 0) < first_decl_line]
    if header_errors:
        raise ProjectError("imports failed: " + "; ".join(header_errors))
    infos: dict[str, DeclInfo] = {}
    for line, name in by_line.items():
        here = [m for m in run.messages if m.line == line]
        errs = [m.text.strip() for m in here if m.severity == "error"]
        if errs:
            infos[name] = DeclInfo(name, False, None, "; ".join(errs))
            continue
        info = [m.text for m in here if m.severity == "information"]
        if not info:
            infos[name] = DeclInfo(name, False, None, "no #check output")
            continue
        text = info[0].strip() if signature else _strip_head(info[0], name)
        infos[name] = DeclInfo(name, True, text)
    return infos

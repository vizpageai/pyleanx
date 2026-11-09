"""Check that a PyLeanX statement *is* a given Lean theorem's statement.

``thm.same_statement_as("OAI.RVM.global_classical_solution")`` asks Lean to prove

    (∀ binders, hypotheses → conclusion) = type_of% @OAI.RVM.global_classical_solution

by ``rfl``, i.e. that the two propositions are definitionally equal (binder names and
implicit/explicit markers do not matter). The check is a normal Lean run with the axiom
audit: any error, or a dependency on ``sorryAx``, means "not shown to be the same".
"""

from __future__ import annotations

import re
import shutil
import uuid
from collections.abc import Iterable
from dataclasses import dataclass, field
from typing import Any

from .names import validate_qualified_name

_CHECK = "pyleanx_same_statement_check"


@dataclass(frozen=True)
class SameStatement:
    """Outcome of a statement comparison (``bool(result)`` is ``same``)."""

    same: bool
    theorem: str
    declaration: str
    lean_source: str
    errors: tuple[str, ...] = ()
    axioms: tuple[str, ...] | None = None
    notes: tuple[str, ...] = field(default=())

    def __bool__(self) -> bool:
        return self.same

    def summary(self) -> str:
        verdict = "SAME statement" if self.same else "NOT shown to be the same"
        out = [f"{self.theorem} vs {self.declaration}: {verdict}"]
        out += [f"  {e.splitlines()[0]}" for e in self.errors[:5]]
        return "\n".join(out)


def statement_term(thm: Any, unicode_types: bool = False) -> str:
    """The theorem's statement as one Lean proposition: ``∀ (x : T) (h : P), C``."""
    from .render.lean import _ExprRenderer, binder_groups

    r = _ExprRenderer(unicode_types)
    binders = []
    if thm.variables:
        binders.append(binder_groups(thm.variables, unicode_types))
    for h in thm.assumptions:
        binders.append(f"({h.name} : {r.render(h.prop)[0]})")
    concl = r.render(thm.conclusion)[0]
    return f"∀ {' '.join(binders)}, {concl}" if binders else concl


def render_check(thm: Any, declaration: str, imports: Iterable[str] = (),
                 unicode_types: bool = False) -> str:
    from .defs import theorem_definitions
    from .imports import resolve_imports

    validate_qualified_name(declaration, "declaration name")
    mods = sorted(set(resolve_imports([thm], list(imports), "minimal", unicode_types)))
    lines = [f"import {m}" for m in mods] + ["", "set_option autoImplicit false", ""]
    for d in theorem_definitions(thm):
        lines += [*d.render(unicode_types), ""]
    lines += [f"theorem {_CHECK} :", f"    ({statement_term(thm, unicode_types)}) =",
              f"      type_of% @{declaration} := rfl", "", f"#print axioms {_CHECK}", ""]
    return "\n".join(lines)


def same_statement(thm: Any, declaration: Any, *, imports: Iterable[str] = (),
                   project: Any = None, timeout: float | None = None) -> SameStatement:
    """Does Lean accept that ``thm``'s statement is definitionally ``declaration``'s type?"""
    from .backend.audit import parse_axiom_report
    from .backend.subprocess_backend import run_lean
    from .project import find_project

    name = getattr(declaration, "name", declaration)
    extra = list(imports) + list(getattr(declaration, "imports", ()) or ())
    proj = find_project(project)
    proj.validate()
    source = render_check(thm, name, extra, proj.unicode_types)
    work = proj.path / ".pyleanx" / "build" / uuid.uuid4().hex
    work.mkdir(parents=True, exist_ok=True)
    f = work / "PyLeanXSame.lean"
    f.write_text(source, encoding="utf-8", newline="\n")
    try:
        run = run_lean(proj, f, timeout if timeout is not None else proj.timeout)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    errors = tuple(m.text.strip() for m in run.messages if m.severity == "error")
    audit_line = source.splitlines().index(f"#print axioms {_CHECK}") + 1
    axioms = None
    for m in run.messages:
        if m.line == audit_line and m.severity == "information":
            rep = parse_axiom_report(m.text)
            if rep is not None and rep.theorem == _CHECK:
                axioms = rep.axioms
    same = (not errors and not run.timed_out and axioms is not None
            and not any(re.search(r"sorry", a) for a in axioms))
    notes = ("Lean timed out",) if run.timed_out else ()
    return SameStatement(same, thm.name, name, source, errors, axioms, notes)

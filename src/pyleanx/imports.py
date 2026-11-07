"""Resolve the minimal explicit Lean imports for a set of theorems.

Imports are derived from (a) sorts used in statements, (b) trusted function
constants, (c) tactics, (d) lemma references with declared imports, and
(e) explicit theorem/project imports. ``import_mode="mathlib"`` replaces all
of them with ``import Mathlib`` (slower but maximally permissive).
"""

from __future__ import annotations

from collections.abc import Iterable
from typing import TYPE_CHECKING

from .expr import App, Cast, Expr, Lit, Quant, iter_subexprs
from .names import validate_qualified_name
from .proofs import Tactic

if TYPE_CHECKING:
    from .theorem import Theorem


def expr_imports(e: Expr) -> list[str]:
    out: list[str] = []
    for sub in iter_subexprs(e):
        if sub.sort is not None:
            out.extend(sub.sort.imports)
        if isinstance(sub, App):
            out.extend(sub.func.imports)
            for a in sub.args:
                if a.sort is not None:
                    out.extend(a.sort.imports)
    return out


def tactic_imports(t: Tactic | None) -> list[str]:
    from .proofs import Branches, Exact, Steps, Use

    if t is None:
        return []
    if isinstance(t, Steps):
        return [i for s in t.tactics for i in tactic_imports(s)]
    if isinstance(t, Branches):
        return [i for s in t.branches for i in tactic_imports(s)]
    out = list(t.imports())
    # Expressions inside tactics (use witnesses, exact terms) may need sort imports.
    if isinstance(t, Use):
        for w in t.witnesses:
            out.extend(expr_imports(w))
    if isinstance(t, Exact) and isinstance(t.term, Expr):
        out.extend(expr_imports(t.term))
    return out


def statement_imports(thm: Theorem) -> list[str]:
    out = [i for v in thm.variables for i in v.sort.imports]
    for part in [thm.conclusion, *(h.prop for h in thm.assumptions)]:
        out.extend(expr_imports(part))
    return out


def statement_sorts(thm: Theorem) -> set:
    """Sorts that can be printed as a type name: binders, casts, ascribed literals.

    (Nat literals are never ascribed, so e.g. the exponent in ``x ^ 2`` adds nothing.)
    """
    sorts = {v.sort for v in thm.variables}
    for part in [thm.conclusion, *(h.prop for h in thm.assumptions)]:
        for sub in iter_subexprs(part):
            if isinstance(sub, Quant):
                sorts.update(v.sort for v in sub.vars)
            elif isinstance(sub, Cast):
                sorts.add(sub.sort)
            elif isinstance(sub, Lit) and sub.sort is not None and sub.sort.name != "Nat":
                sorts.add(sub.sort)
    return sorts


def resolve_imports(
    theorems: Iterable[Theorem],
    extra: Iterable[str] = (),
    mode: str = "minimal",
    unicode_types: bool = False,
) -> tuple[str, ...]:
    if mode == "mathlib":
        return ("Mathlib",)
    if mode != "minimal":
        raise ValueError(f"unknown import mode {mode!r} (use 'minimal' or 'mathlib')")
    mods: set[str] = set()
    for thm in theorems:
        mods.update(statement_imports(thm))
        mods.update(tactic_imports(thm.proof))
        mods.update(thm.imports)
        if unicode_types:
            mods.update(i for s in statement_sorts(thm) for i in s.unicode_imports)
    mods.update(extra)
    for m in mods:
        validate_qualified_name(m, "import module")
    return tuple(sorted(mods))

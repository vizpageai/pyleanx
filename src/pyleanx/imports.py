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


#: Modules that define the notation of the general term nodes (checked at the pinned Mathlib).
NOTATION_IMPORTS = {
    "sum": ("Mathlib.Algebra.BigOperators.Group.Finset.Defs",),
    "prod": ("Mathlib.Algebra.BigOperators.Group.Finset.Defs",),
    "integral": ("Mathlib.MeasureTheory.Integral.Bochner.Basic",),
    "interval_integral": ("Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic",),
    "norm": ("Mathlib.Analysis.Normed.Group.Basic",),
    "smul": ("Mathlib.Algebra.Group.Defs",),
}


def expr_imports(e: Expr) -> list[str]:
    from .expr import BinOp
    from .terms import BigOp, Const, Lam, Norm, TypeTerm

    out: list[str] = []
    for sub in iter_subexprs(e):
        if sub.sort is not None:
            out.extend(sub.sort.imports)
        if isinstance(sub, App):
            out.extend(sub.func.imports)
            for a in sub.args:
                if a.sort is not None:
                    out.extend(a.sort.imports)
        elif isinstance(sub, Const):
            out.extend(sub.imports)
            if sub.definition is not None:
                out.extend(sub.definition.imports())
        elif isinstance(sub, TypeTerm):
            out.extend(sub.type.imports)
        elif isinstance(sub, Lam):
            out.extend(i for v in sub.vars for i in v.sort.imports)
        elif isinstance(sub, BigOp):
            out.extend(sub.var.sort.imports)
            key = "interval_integral" if sub.bounds is not None else sub.kind
            out.extend(NOTATION_IMPORTS[key])
        elif isinstance(sub, Norm):
            out.extend(NOTATION_IMPORTS["norm"])
        elif isinstance(sub, BinOp) and sub.op == "smul":
            out.extend(NOTATION_IMPORTS["smul"])
        elif isinstance(sub, Quant):
            out.extend(i for v in sub.vars for i in v.sort.imports)
    return out


def tactic_imports(t: Tactic | None) -> list[str]:
    from .defs import proof_exprs

    if t is None:
        return []
    out = list(t.imports())
    for sub in t.sub_tactics():  # nested blocks (have/calc/induction/steps/branches)
        out.extend(tactic_imports(sub))
    # Expressions inside tactics (witnesses, terms, have/calc statements) need their imports.
    for e in proof_exprs(t):
        out.extend(expr_imports(e))
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
    from .defs import theorem_definitions

    mods: set[str] = set()
    for thm in theorems:
        for d in theorem_definitions(thm):
            mods.update(d.imports())
        mods.update(statement_imports(thm))
        mods.update(tactic_imports(thm.proof))
        mods.update(thm.imports)
        if unicode_types:
            mods.update(i for s in statement_sorts(thm) for i in s.unicode_imports)
    mods.update(extra)
    for m in mods:
        validate_qualified_name(m, "import module")
    return tuple(sorted(mods))

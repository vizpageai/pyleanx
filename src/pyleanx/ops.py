"""Operations on statements: the term algebra that proof moves are built from.

As tensor operations are to PyTorch, these are to PyLeanX: every move of a written proof
(instantiate a fact, "similarly" with points exchanged, unfold a definition, show P(k + 1)
in an induction) is one of them applied to a statement. They are pure: a statement is
immutable, and the result is a new statement. Python never decides what is true; Lean
checks every statement a proof produces.

    from pyleanx import ops
    ops.free_vars(e)                     # [x, y] in first-occurrence order
    ops.substitute(e, (x, 0))            # e[x := 0]
    ops.exchange(e, (A, B))              # A and B swapped simultaneously
    ops.same(e1, e2)                     # structurally identical
    ops.vocabulary(thm)                  # sorts and Lean symbols a theorem uses
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator
from typing import Any

from .binders import free_vars as _free_vars
from .binders import substitute as _substitute
from .expr import App, Expr, Lit, Var, _lift, iter_subexprs


def free_vars(e: Expr) -> list[Var]:
    """The free variables of ``e``, in first-occurrence order (bound ones excluded)."""
    return _free_vars(e)


def substitute(e: Expr, *pairs: tuple[Var, object]) -> Expr:
    """``e`` with free variables replaced simultaneously: ``substitute(e, (x, 0), (y, z))``.

    Values may be Python numbers. A binder that rebinds a replaced variable stops the
    replacement below it. (Variables cannot be dictionary keys, since ``x == y`` builds an
    equation; hence pairs.)
    """
    mapping: dict[int, Expr] = {}
    for pair in pairs:
        if not (isinstance(pair, tuple) and len(pair) == 2 and isinstance(pair[0], Var)):
            raise TypeError("substitute: pairs (variable, value), e.g. ops.substitute(e, (x, 0))")
        value = _lift(pair[1])
        sort = pair[0].sort
        if isinstance(value, Lit) and value.sort is None and getattr(sort, "numeric", False):
            value = Lit(value.value, sort)  # a number takes the variable's sort
        mapping[pair[0].uid] = value
    return _substitute(e, mapping)


def exchange(e: Expr, *pairs: tuple[Var, Var]) -> Expr:
    """``e`` with each pair of variables swapped simultaneously ("similarly", by symmetry)."""
    mapping: dict[int, Expr] = {}
    for pair in pairs:
        if not (isinstance(pair, tuple) and len(pair) == 2
                and all(isinstance(v, Var) for v in pair)):
            raise TypeError("exchange: pairs of variables, e.g. ops.exchange(e, (A, B))")
        a, b = pair
        mapping[a.uid], mapping[b.uid] = b, a
    return _substitute(e, mapping)


def same(a: Expr, b: Expr) -> bool:
    """Are ``a`` and ``b`` the same statement, symbol for symbol (not up to logic)?"""
    return bool(a._key() == b._key())


def subterms(e: Expr) -> Iterator[Expr]:
    """``e`` and every expression inside it."""
    return iter(iter_subexprs(e))


def sorts(e: Expr) -> set[str]:
    """Names of the sorts occurring in ``e`` (of its subterms and bound variables)."""
    out: set[str] = set()
    for sub in iter_subexprs(e):
        for s in (sub.sort, *(v.sort for v in getattr(sub, "vars", ()))):
            name = getattr(s, "name", None)
            if isinstance(name, str):
                out.add(name)
    return out


def symbols(e: Expr) -> set[str]:
    """Lean names of the functions and constants ``e`` applies."""
    from .terms import Apply, Const

    out: set[str] = set()
    for sub in iter_subexprs(e):
        if isinstance(sub, App):
            out.add(sub.func.lean_name)
        elif isinstance(sub, Apply) and isinstance(sub.fn, Const):
            out.add(sub.fn.name)
    return out


def vocabulary(thm: Any) -> tuple[set[str], set[str]]:
    """The sorts and Lean symbols a theorem uses: its variables, statement, hypotheses and
    every statement of its proof. Domain packs are activated by this vocabulary."""
    from .defs import proof_exprs

    found_sorts: set[str] = set()
    for v in thm.variables:
        name = getattr(v.sort, "name", None)
        if isinstance(name, str):
            found_sorts.add(name)
    exprs: Iterable[Expr] = [thm.conclusion, *(h.prop for h in thm.assumptions)]
    if thm.proof is not None:
        exprs = [*exprs, *proof_exprs(thm.proof)]
    found_symbols: set[str] = set()
    for e in exprs:
        found_sorts |= sorts(e)
        found_symbols |= symbols(e)
    return found_sorts, found_symbols


__all__ = ["exchange", "free_vars", "same", "sorts", "substitute", "subterms", "symbols",
           "vocabulary"]

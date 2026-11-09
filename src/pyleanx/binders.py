"""Variables and quantifier scoping.

Every :class:`~pyleanx.expr.Var` has a unique ``uid``; two variables with the
same user name are *different* variables. Scope validation rejects free
variables, rebinding and name capture/shadowing before any Lean is emitted, so
the rendered Lean text always means exactly what the IR means.
"""

from __future__ import annotations

from collections.abc import Iterable

from ._origin import caller_origin
from .errors import ScopeError
from .expr import Expr, Quant, Var, make_var
from .types import Prop, Sort

__all__ = ["symbol", "symbols", "prop_symbol", "free_vars", "check_scope"]


def symbol(name: str, sort: Sort) -> Var:
    """Create one fresh variable: ``x = pl.symbol("x", pl.Real)``."""
    return make_var(name, sort, caller_origin())


def symbols(names: str | Iterable[str], sort: Sort) -> tuple[Var, ...]:
    """``x, y = pl.symbols("x y", pl.Real)`` (space- or comma-separated)."""
    if isinstance(names, str):
        parts = names.replace(",", " ").split()
    else:
        parts = list(names)
    if not parts:
        raise ScopeError("symbols() needs at least one name")
    origin = caller_origin()
    return tuple(make_var(n, sort, origin) for n in parts)


def prop_symbol(name: str) -> Var:
    """A proposition variable ``(P : Prop)``."""
    return make_var(name, Prop, caller_origin())


def free_vars(e: Expr) -> list[Var]:
    """Free variables of ``e`` in first-occurrence order (by identity)."""
    out: list[Var] = []
    seen: set[int] = set()

    def walk(node: Expr, bound: frozenset[int]) -> None:
        if isinstance(node, Var):
            if node.uid not in bound and node.uid not in seen:
                seen.add(node.uid)
                out.append(node)
            return
        binder = _binder(node)
        if binder is not None:
            vs, body, outer = binder
            for o in outer:
                walk(o, bound)
            walk(body, bound | {v.uid for v in vs})
            return
        for child in node.children():
            walk(child, bound)

    walk(e, frozenset())
    return out


def _binder(node: Expr) -> tuple[tuple[Var, ...], Expr, tuple[Expr, ...]] | None:
    """(bound variables, body, sub-terms outside the binder) for binding nodes."""
    if isinstance(node, Quant):
        return node.vars, node.body, ()
    from .terms import BigOp, Lam

    if isinstance(node, Lam):
        return node.vars, node.body, ()
    if isinstance(node, BigOp):
        outer = tuple(c for c in node.children() if c is not node.body)
        return node.vars, node.body, outer
    return None


def check_scope(e: Expr, context: dict[str, Var], where: str) -> None:
    """Validate ``e`` under ``context`` (name -> Var in scope).

    Raises :class:`ScopeError` on free/undeclared variables, on rebinding a variable
    that is already in scope, and on binders whose *name* would shadow (capture)
    another variable in scope.
    """

    def walk(node: Expr, ctx: dict[str, Var]) -> None:
        if isinstance(node, Var):
            bound = ctx.get(node.name)
            if bound is None or bound.uid != node.uid:
                hint = ""
                if bound is not None:
                    hint = f" (a different variable named {node.name!r} is in scope)"
                raise ScopeError(
                    f"{where}: variable {node.name!r} is not declared{hint}. Add it to "
                    "Theorem(variables=[...]) or bind it with pl.Forall/pl.Exists"
                    + (f" [created at {node.origin}]" if node.origin else "")
                )
            return
        binder = _binder(node)
        if binder is not None:
            vs, body, outer = binder
            for o in outer:
                walk(o, ctx)
            inner = dict(ctx)
            for v in vs:
                if v.name in inner:
                    other = inner[v.name]
                    kind = "rebinds" if other.uid == v.uid else "shadows another variable named"
                    raise ScopeError(
                        f"{where}: {getattr(node, 'kind', 'fun')} {kind} {v.name!r}; use a "
                        "fresh name to avoid variable capture"
                    )
                inner[v.name] = v
            walk(body, inner)
            return
        for child in node.children():
            walk(child, ctx)

    walk(e, context)


def contains_untyped_literal(e: Expr) -> bool:
    """An untyped numeral whose sort PyLeanX must know (i.e. outside open Lean types,
    where Lean elaborates numerals at the expected type)."""

    def opaque_ctx(node: Expr) -> bool:
        from .terms import Apply, Ascribe, BigOp, Lam

        if isinstance(node, (Apply, Lam, BigOp, Ascribe)):
            return True
        return any(c.sort is not None and c.sort.opaque for c in node.children())

    def walk(node: Expr, opaque: bool) -> bool:
        if node.sort is None and not opaque and not node.children():
            return True
        here = opaque or opaque_ctx(node) or (node.sort is not None and node.sort.opaque)
        return any(walk(c, here) for c in node.children())

    return walk(e, False)

"""General Lean terms: constants, application, ``fun``, big operators, pairs, fields.

These nodes let PyLeanX statements use any Lean/Mathlib vocabulary, not only the built-in
sorts and functions. Python checks *scope* (every variable is bound) and *syntax*; the types
are checked by Lean's elaborator, whose errors are mapped back to the Python line.

    V = pl.EuclideanSpace(3)
    f = pl.var("f", pl.Fn(V, pl.Real))
    x = pl.var("x", V)
    pl.fun(lambda y: f(y) * 2)              # fun (y : EuclideanSpace ℝ (Fin 3)) => f y * 2
    pl.sum(pl.Fin(3), lambda i: x(i)**2)    # ∑ i : Fin 3, x i ^ 2
"""

from __future__ import annotations

import inspect
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from typing import Any

from ._origin import caller_origin, resolve_annotations
from .errors import SortError
from .expr import BinOp, Expr, Var, _lift, make_var
from .names import validate_identifier, validate_qualified_name
from .types import TYPE, UNKNOWN, LeanType, Prop, Real, Sort

__all__ = [
    "Const", "Apply", "Lam", "BigOp", "TypeTerm", "Pair", "Field", "Ascribe", "Norm",
    "const", "apply", "fun", "sum", "prod", "integral", "pair", "field", "ascribe", "smul",
    "norm", "var", "type_term",
]

_RESERVED = {"sorry", "sorryAx", "admit", "lcProof", "Lean.ofReduceBool", "Lean.trustCompiler"}


@dataclass(frozen=True, eq=False, repr=False)
class Const(Expr):
    """A Lean constant (library declaration or PyLeanX definition) used as a term."""

    name: str
    sort: Sort
    imports: tuple[str, ...] = ()
    latex: str = ""
    definition: Any = None  # a pyleanx.defs.Definition when this is a PyLeanX definition
    arity: int | None = None  # explicit arguments, when known (from bindings)
    result: Sort | None = None  # sort after ``arity`` explicit arguments, when known

    def __post_init__(self) -> None:
        validate_qualified_name(self.name, "constant name")
        if self.name in _RESERVED:
            raise SortError(f"{self.name} cannot be used as a term")

    def _key(self) -> tuple:
        return ("const", self.name)

    def canonical(self) -> Any:
        if self.definition is not None:
            return ["defref", self.name]
        return ["const", self.name, self.sort.canonical(), list(self.imports), self.arity,
                self.result.canonical() if self.result is not None else None]


@dataclass(frozen=True, eq=False, repr=False)
class Apply(Expr):
    """``fn arg₁ … argₙ`` for any function-valued term."""

    fn: Expr
    args: tuple[Expr, ...]
    sort: Sort

    def _key(self) -> tuple:
        return ("apply", self.fn._key(), tuple(a._key() for a in self.args))

    def canonical(self) -> Any:
        return ["apply", self.fn.canonical(), [a.canonical() for a in self.args],
                self.sort.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.fn, *self.args)


@dataclass(frozen=True, eq=False, repr=False)
class TypeTerm(Expr):
    """A type used as an argument, e.g. the ℝ in ``fderiv ℝ f x``."""

    type: Sort
    sort: Sort = TYPE

    def _key(self) -> tuple:
        return ("typeterm", self.type.canonical().__repr__())

    def canonical(self) -> Any:
        return ["typeterm", self.type.canonical()]


@dataclass(frozen=True, eq=False, repr=False)
class Lam(Expr):
    """``fun (x : A) (y : B) => body``."""

    vars: tuple[Var, ...]
    body: Expr
    sort: Sort

    def _key(self) -> tuple:
        return ("lam", tuple(v.uid for v in self.vars), self.body._key())

    def canonical(self) -> Any:
        return ["lam", [v.canonical() for v in self.vars], self.body.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.body,)


BIG_OPS = {"sum": "∑", "prod": "∏", "integral": "∫"}


@dataclass(frozen=True, eq=False, repr=False)
class BigOp(Expr):
    """``∑ i : Fin 3, body``, ``∏ i ∈ s, body``, ``∫ x : V, body``, ``∫ x in a..b, body``."""

    kind: str
    var: Var
    body: Expr
    sort: Sort
    over: Expr | None = None  # a Finset (sum/prod) or None (whole type)
    bounds: tuple[Expr, Expr] | None = None  # interval integral a..b

    def _key(self) -> tuple:
        extra = (self.over._key() if self.over is not None else None,
                 tuple(b._key() for b in self.bounds) if self.bounds else None)
        return ("bigop", self.kind, self.var.uid, self.body._key(), extra)

    @property
    def vars(self) -> tuple[Var, ...]:
        return (self.var,)

    def canonical(self) -> Any:
        return ["bigop", self.kind, self.var.canonical(), self.body.canonical(),
                self.over.canonical() if self.over is not None else None,
                [b.canonical() for b in self.bounds] if self.bounds else None]

    def children(self) -> tuple[Expr, ...]:
        out: list[Expr] = []
        if self.over is not None:
            out.append(self.over)
        if self.bounds:
            out.extend(self.bounds)
        return (*out, self.body)

    def binder_children(self) -> tuple[Expr, ...]:
        return (self.body,)


@dataclass(frozen=True, eq=False, repr=False)
class Pair(Expr):
    fst: Expr
    snd: Expr
    sort: Sort

    def _key(self) -> tuple:
        return ("pair", self.fst._key(), self.snd._key())

    def canonical(self) -> Any:
        return ["pair", self.fst.canonical(), self.snd.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.fst, self.snd)


@dataclass(frozen=True, eq=False, repr=False)
class Field(Expr):
    """``e.name`` (structure field or ``fst``/``snd``/``1``/``2`` projection)."""

    arg: Expr
    name: str
    sort: Sort

    def _key(self) -> tuple:
        return ("field", self.arg._key(), self.name)

    def canonical(self) -> Any:
        return ["field", self.arg.canonical(), self.name, self.sort.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.arg,)


@dataclass(frozen=True, eq=False, repr=False)
class Ascribe(Expr):
    """``(e : T)``: tells Lean the intended type (and Python the sort)."""

    arg: Expr
    sort: Sort

    def _key(self) -> tuple:
        return ("ascribe", self.arg._key(), repr(self.sort.canonical()))

    def canonical(self) -> Any:
        return ["ascribe", self.arg.canonical(), self.sort.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.arg,)


@dataclass(frozen=True, eq=False, repr=False)
class Norm(Expr):
    """``‖e‖``."""

    arg: Expr
    sort: Sort = Real

    def _key(self) -> tuple:
        return ("norm", self.arg._key())

    def canonical(self) -> Any:
        return ["norm", self.arg.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.arg,)


@dataclass(frozen=True, eq=False, repr=False)
class StructLit(Expr):
    """``({ f0 := a, E0 := b } : T)``."""

    values: tuple[tuple[str, Expr], ...]
    sort: Sort

    def _key(self) -> tuple:
        return ("structlit", self.sort.name, tuple((n, v._key()) for n, v in self.values))

    def canonical(self) -> Any:
        return ["structlit", self.sort.canonical(), [[n, v.canonical()] for n, v in self.values]]

    def children(self) -> tuple[Expr, ...]:
        return tuple(v for _, v in self.values)


# =====================================================================================
# Constructors
# =====================================================================================


def _arg(value: object) -> Expr:
    if isinstance(value, Sort):
        return TypeTerm(value)
    return _lift(value)


def var(name: str, sort: Sort) -> Var:
    """A variable of any sort, including open Lean types: ``pl.var("f", pl.Fn(V, pl.Real))``."""
    return make_var(name, sort, caller_origin())


def type_term(sort: Sort) -> TypeTerm:
    """Use a type as a term argument (``fderiv ℝ …``); sorts passed to calls convert
    automatically."""
    return TypeTerm(sort)


def const(name: str, sort: Sort = UNKNOWN, imports: Iterable[str] = (), *,
          latex: str = "") -> Const:
    """A Lean declaration as a term: ``pl.const("Real.pi", pl.Real, ["Mathlib…"])``.

    Prefer generated bindings (``pyleanx.lib``), which know each declaration's module and
    argument structure. ``sort`` defaults to unknown (Lean infers the type).
    """
    imps = tuple(validate_qualified_name(i, "import module") for i in imports)
    return Const(name, sort, imps, latex)


def _result_sort(fn: Expr, n: int) -> Sort:
    s = fn.sort
    if isinstance(fn, Const) and fn.arity is not None:
        if n == fn.arity and fn.result is not None:
            return fn.result
        return UNKNOWN
    if isinstance(s, LeanType) and s.kind == "fn":
        dom = s.parts[:-1]
        if n > len(dom):
            raise SortError(f"{fn} takes {len(dom)} argument(s), got {n}")
        if n == len(dom):
            return s.parts[-1]
        from .types import Fn

        return Fn(*s.parts[n:])
    if s is UNKNOWN or (isinstance(s, LeanType) and s.kind == "type"):
        return UNKNOWN
    raise SortError(f"{fn} has sort {s.name if s else 'numeral'} and cannot be applied")


def apply(fn: object, *args: object) -> Expr:
    """``fn a b …`` (also written ``fn(a, b)`` on any function-valued term)."""
    f = _lift(fn)
    if not args:
        raise SortError("apply needs at least one argument")
    conv = tuple(_arg(a) for a in args)
    sort = _result_sort(f, len(conv))
    if isinstance(f, Apply):  # flatten curried applications
        return Apply(f.fn, f.args + conv, sort)
    return Apply(f, conv, sort)


def _fresh_params(fn: Callable[..., Any], sorts: Iterable[Sort] | Sort | None,
                  what: str) -> list[Var]:
    sig = inspect.signature(fn)
    params = list(sig.parameters.values())
    if sorts is None:
        hints = resolve_annotations(fn, 3) if hasattr(fn, "__code__") else {}
        chosen = [hints.get(p.name) for p in params]
    elif isinstance(sorts, Sort):
        chosen = [sorts] * len(params)
    else:
        chosen = list(sorts)
    if len(chosen) != len(params) or not all(isinstance(s, Sort) for s in chosen):
        raise SortError(f"{what}: give the bound variable sorts, e.g. pl.fun(lambda x: ..., "
                        "pl.Real) or annotate the parameters")
    origin = caller_origin()
    return [make_var(p.name, s, origin)  # type: ignore[arg-type]  # checked above
            for p, s in zip(params, chosen, strict=True)]


def fun(body: Callable[..., object], sorts: Iterable[Sort] | Sort | None = None) -> Lam:
    """``fun x => …`` from a Python function, called once with fresh bound variables.

    ``pl.fun(lambda x: x**2 + 1, pl.Real)``; with several parameters pass a list of sorts.
    """
    vs = _fresh_params(body, sorts, "pl.fun")
    if not vs:
        raise SortError("pl.fun needs at least one parameter")
    out = _lift(body(*vs))
    from .types import Fn

    return Lam(tuple(vs), out, Fn(*(v.sort for v in vs), out.sort or UNKNOWN))


def _bigop(kind: str, over: object, body: Callable[..., object], sort: Sort | None,
           bounds: tuple[object, object] | None = None) -> BigOp:
    dom: Sort | None
    set_expr: Expr | None
    if isinstance(over, Sort):
        dom, set_expr = over, None
    else:
        dom, set_expr = sort, (_lift(over) if over is not None else None)
        if dom is None:
            raise SortError(f"pl.{kind} over a set needs the element sort: "
                            f"pl.{kind}(s, lambda i: ..., sort=pl.Nat)")
    (v,) = _fresh_params(body, dom, f"pl.{kind}")
    out = _lift(body(v))
    bnds = tuple(_lift(b) for b in bounds) if bounds else None
    return BigOp(kind, v, out, out.sort or UNKNOWN, set_expr, bnds)  # type: ignore[arg-type]


def sum(over: object, body: Callable[..., object], *, sort: Sort | None = None) -> BigOp:  # noqa: A001
    """``∑ i : T, body i`` (``over`` a finite type such as ``pl.Fin(3)``) or ``∑ i ∈ s, …``."""
    return _bigop("sum", over, body, sort)


def prod(over: object, body: Callable[..., object], *, sort: Sort | None = None) -> BigOp:
    """``∏ i : T, body i`` or ``∏ i ∈ s, body i``."""
    return _bigop("prod", over, body, sort)


def integral(body: Callable[..., object], over: Sort = Real, *,
             bounds: tuple[object, object] | None = None) -> BigOp:
    """``∫ x : T, body x`` (Lebesgue/Bochner, volume measure) or ``∫ x in a..b, body x``."""
    return _bigop("integral", over, body, over, bounds)


def pair(a: object, b: object) -> Pair:
    """The pair ``(a, b)``."""
    ea, eb = _lift(a), _lift(b)
    from .types import Prod

    return Pair(ea, eb, Prod(ea.sort or UNKNOWN, eb.sort or UNKNOWN))


def field(e: object, name: str) -> Field:
    """``e.name``: a structure field, or ``fst``/``snd``/``1``/``2`` of a pair."""
    ex = _lift(e)
    s = ex.sort
    if name in ("1", "2", "fst", "snd"):
        if isinstance(s, LeanType) and s.kind == "prod":
            idx = 0 if name in ("1", "fst") else 1
            part = s.parts[idx] if len(s.parts) == 2 or idx == 0 else UNKNOWN
            if idx == 1 and len(s.parts) > 2:
                from .types import Prod

                part = Prod(*s.parts[1:])
            return Field(ex, name, part)
        return Field(ex, name, UNKNOWN)
    fsort = s.field_sort(name) if isinstance(s, LeanType) else None
    if fsort is None and isinstance(s, LeanType) and s.kind == "struct":
        # Python identifiers cannot contain ₀…₉: `d.f0` means the Lean field `f₀`.
        from .bindings import ascii_alias

        real = next((n for n, _ in s.fields if ascii_alias(n) == name), None)
        if real is not None:
            name, fsort = real, s.field_sort(real)
    validate_identifier(name, "field name")
    if isinstance(s, LeanType) and s.kind == "struct" and fsort is None:
        raise AttributeError(f"structure {s.name} has no field {name!r}; fields: "
                             f"{[n for n, _ in s.fields]}")
    return Field(ex, name, fsort or UNKNOWN)


def ascribe(e: object, sort: Sort) -> Ascribe:
    """``(e : T)``."""
    return Ascribe(_lift(e), sort)


def smul(c: object, v: object) -> Expr:
    """Scalar multiplication ``c • v``."""
    ec, ev = _lift(c), _lift(v)
    return BinOp("smul", ec, ev, ev.sort if ev.sort is not None else UNKNOWN)


def norm(e: object) -> Norm:
    """The norm ``‖e‖`` (a real number)."""
    return Norm(_lift(e))


def is_prop_sort(s: Sort | None) -> bool:
    return s is Prop

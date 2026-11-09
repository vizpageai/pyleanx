"""Immutable, typed expression IR with operator overloading.

Like a ``torch.Tensor`` builds an autograd graph, a PyLeanX :class:`Expr` builds
an expression tree. Nothing is evaluated in Python: ``x + y == y + x`` is a
*proposition* object that only Lean can decide.

Pitfalls handled here:

* ``__eq__`` returns a proposition, so ``Expr`` objects are unhashable and must
  not be used as dict keys / set members; use :meth:`Expr.same_structure`.
* ``__bool__`` raises :class:`SymbolicTruthValueError` (this catches ``and``,
  ``or``, ``not``, ``if``, chained comparisons and builtin ``min``/``max``).
* Python ``float`` and ``bool`` are rejected as literals; use ``pl.real("0.1")``
  or ``pl.rat(1, 10)``.
* No implicit coercion between sorts; use :func:`cast`.
"""

from __future__ import annotations

import itertools
from collections.abc import Iterable, Sequence
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

from ._origin import Origin, caller_origin
from .errors import LiteralError, ScopeError, SortError, SymbolicTruthValueError
from .names import validate_identifier, validate_qualified_name
from .types import Int, Nat, Prop, Real, Sort, can_cast

_uid_counter = itertools.count(1)


def _next_uid() -> int:
    return next(_uid_counter)


class Expr:
    """Base class of all symbolic expressions (terms and propositions)."""

    __slots__ = ()

    # Subclasses set ``sort``; ``None`` means an as-yet-untyped numeral.
    sort: Sort | None

    # ---- Python truthiness / conversion pitfalls --------------------------------
    def __bool__(self) -> bool:
        raise SymbolicTruthValueError(_safe_text(self))

    def __float__(self) -> float:
        raise TypeError("symbolic expressions cannot be converted to float")

    def __int__(self) -> int:
        raise TypeError("symbolic expressions cannot be converted to int")

    def __index__(self) -> int:
        raise TypeError("symbolic expressions cannot be used as Python indices/ranges")

    def __iter__(self):
        raise TypeError("symbolic expressions are not iterable")

    __hash__ = None  # type: ignore[assignment]  # __eq__ is symbolic

    # ---- comparisons build propositions -----------------------------------------
    def __eq__(self, other: object) -> Compare:  # type: ignore[override]
        return _compare("eq", self, other)

    def __ne__(self, other: object) -> Compare:  # type: ignore[override]
        return _compare("ne", self, other)

    def __lt__(self, other: object) -> Compare:
        return _compare("lt", self, other)

    def __le__(self, other: object) -> Compare:
        return _compare("le", self, other)

    def __gt__(self, other: object) -> Compare:
        return _compare("gt", self, other)

    def __ge__(self, other: object) -> Compare:
        return _compare("ge", self, other)

    # ---- arithmetic --------------------------------------------------------------
    def __add__(self, other: object) -> Expr:
        return _arith("add", self, other)

    def __radd__(self, other: object) -> Expr:
        return _arith("add", other, self)

    def __sub__(self, other: object) -> Expr:
        return _arith("sub", self, other)

    def __rsub__(self, other: object) -> Expr:
        return _arith("sub", other, self)

    def __mul__(self, other: object) -> Expr:
        return _arith("mul", self, other)

    def __rmul__(self, other: object) -> Expr:
        return _arith("mul", other, self)

    def __truediv__(self, other: object) -> Expr:
        return _arith("div", self, other)

    def __rtruediv__(self, other: object) -> Expr:
        return _arith("div", other, self)

    def __floordiv__(self, other: object) -> Expr:
        return _floordiv(self, other)

    def __rfloordiv__(self, other: object) -> Expr:
        return _floordiv(other, self)

    def __mod__(self, other: object) -> Expr:
        return _mod(self, other)

    def __rmod__(self, other: object) -> Expr:
        return _mod(other, self)

    def __pow__(self, other: object) -> Expr:
        return _pow(self, other)

    def __rpow__(self, other: object) -> Expr:
        return _pow(other, self)

    def __neg__(self) -> Expr:
        e = _as_numeric_term(self, "unary minus")
        if e.sort is not None and not e.sort.allows_negation:
            raise SortError(
                "unary minus is not available on Nat; cast to Int first: -pl.cast(n, pl.Int)"
            )
        if isinstance(e, Lit):
            return Lit(-e.value, e.sort)
        return Neg(e, e.sort)

    def __pos__(self) -> Expr:
        return self

    def __abs__(self) -> Expr:
        return abs_(self)

    # ---- logic (bitwise operators on propositions) -------------------------------
    def __and__(self, other: object) -> Expr:
        return And(self, other)

    def __rand__(self, other: object) -> Expr:
        return And(other, self)

    def __or__(self, other: object) -> Expr:
        return Or(self, other)

    def __ror__(self, other: object) -> Expr:
        return Or(other, self)

    def __invert__(self) -> Expr:
        return Not(self)

    # ---- structural API ----------------------------------------------------------
    def same_structure(self, other: Expr) -> bool:
        """Structural equality (variables compared by identity)."""
        if not isinstance(other, Expr):
            return False
        return self._key() == other._key()

    def _key(self) -> tuple:  # pragma: no cover - abstract
        raise NotImplementedError

    def canonical(self) -> Any:
        """JSON-serialisable canonical form (variables by name and sort)."""
        raise NotImplementedError  # pragma: no cover - abstract

    def children(self) -> tuple[Expr, ...]:
        return ()

    @property
    def is_prop(self) -> bool:
        return self.sort is Prop

    def to_lean(self) -> str:
        """Render this expression alone as Lean syntax (for display)."""
        from .render.lean import render_expr

        return render_expr(self)

    def __repr__(self) -> str:
        return f"<pl.{type(self).__name__} {_safe_text(self)}>"

    def __str__(self) -> str:
        return _safe_text(self)

    def to_latex(self) -> str:
        """LaTeX for display only (Jupyter, papers). Lean never sees this."""
        from .render.latex import expr_to_latex

        return expr_to_latex(self)

    def _repr_latex_(self) -> str:  # Jupyter renders this as math
        try:
            return f"${self.to_latex()}$"
        except Exception:  # pragma: no cover - display must never fail
            return f"`{_safe_text(self)}`"


def _safe_text(e: Expr) -> str:
    try:
        return e.to_lean()
    except Exception:  # pragma: no cover - repr must never fail
        return type(e).__name__


# =====================================================================================
# Leaves
# =====================================================================================


@dataclass(frozen=True, eq=False, repr=False)
class Var(Expr):
    """A named variable. Identity is the ``uid``; ``name`` is what Lean sees."""

    name: str
    sort: Sort
    uid: int = field(default_factory=_next_uid)
    origin: Origin | None = None

    def _key(self) -> tuple:
        return ("var", self.uid)

    def canonical(self) -> Any:
        return ["var", self.name, self.sort.name]


@dataclass(frozen=True, eq=False, repr=False)
class Lit(Expr):
    """Exact numeric literal. ``sort is None`` means 'takes the sort of its context'."""

    value: Fraction
    sort: Sort | None = None

    def __post_init__(self) -> None:
        if self.sort is not None:
            _check_literal_fits(self.value, self.sort)

    def _key(self) -> tuple:
        return ("lit", self.value, self.sort.name if self.sort else None)

    def canonical(self) -> Any:
        return ["lit", str(self.value), self.sort.name if self.sort else None]


@dataclass(frozen=True, eq=False, repr=False)
class PropConst(Expr):
    value: bool
    sort: Sort = Prop

    def _key(self) -> tuple:
        return ("propconst", self.value)

    def canonical(self) -> Any:
        return ["propconst", self.value]


TRUE = PropConst(True)
FALSE = PropConst(False)


# =====================================================================================
# Arithmetic
# =====================================================================================

ARITH_OPS = ("add", "sub", "mul", "div", "mod", "pow")


@dataclass(frozen=True, eq=False, repr=False)
class BinOp(Expr):
    op: str
    lhs: Expr
    rhs: Expr
    sort: Sort | None

    def _key(self) -> tuple:
        return ("binop", self.op, self.lhs._key(), self.rhs._key())

    def canonical(self) -> Any:
        return [self.op, self.lhs.canonical(), self.rhs.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.lhs, self.rhs)


@dataclass(frozen=True, eq=False, repr=False)
class Neg(Expr):
    arg: Expr
    sort: Sort | None

    def _key(self) -> tuple:
        return ("neg", self.arg._key())

    def canonical(self) -> Any:
        return ["neg", self.arg.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.arg,)


@dataclass(frozen=True, eq=False, repr=False)
class Cast(Expr):
    """Explicit embedding, rendered ``(↑(e) : Real)``."""

    arg: Expr
    sort: Sort

    def _key(self) -> tuple:
        return ("cast", self.sort.name, self.arg._key())

    def canonical(self) -> Any:
        return ["cast", self.sort.name, self.arg.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.arg,)


@dataclass(frozen=True)
class Func:
    """A trusted, typed Lean function constant (e.g. ``Real.sqrt : Real -> Real``)."""

    lean_name: str
    arg_sorts: tuple[Sort, ...]
    result_sort: Sort
    imports: tuple[str, ...] = ()
    #: Display only. A template with ``{0}``, ``{1}``... placeholders (e.g.
    #: ``r"\angle {0}{1}{2}"``) or an operator name such as ``r"\sin"``.
    latex: str = ""

    def __post_init__(self) -> None:
        validate_qualified_name(self.lean_name, "function name")

    def __call__(self, *args: object) -> App:
        if len(args) != len(self.arg_sorts):
            raise SortError(
                f"{self.lean_name} expects {len(self.arg_sorts)} argument(s), got {len(args)}"
            )
        pairs = zip(args, self.arg_sorts, strict=True)
        conv = tuple(_coerce_to(a, s, self.lean_name) for a, s in pairs)
        return App(self, conv, self.result_sort)


@dataclass(frozen=True, eq=False, repr=False)
class App(Expr):
    func: Func
    args: tuple[Expr, ...]
    sort: Sort

    def _key(self) -> tuple:
        return ("app", self.func.lean_name, tuple(a._key() for a in self.args))

    def canonical(self) -> Any:
        return ["app", self.func.lean_name, [a.canonical() for a in self.args]]

    def children(self) -> tuple[Expr, ...]:
        return self.args


# =====================================================================================
# Propositions
# =====================================================================================

COMPARE_OPS = ("eq", "ne", "lt", "le", "gt", "ge")


@dataclass(frozen=True, eq=False, repr=False)
class Compare(Expr):
    op: str
    lhs: Expr
    rhs: Expr
    sort: Sort = Prop

    def _key(self) -> tuple:
        return ("cmp", self.op, self.lhs._key(), self.rhs._key())

    def canonical(self) -> Any:
        return [self.op, self.lhs.canonical(), self.rhs.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.lhs, self.rhs)


@dataclass(frozen=True, eq=False, repr=False)
class NotP(Expr):
    arg: Expr
    sort: Sort = Prop

    def _key(self) -> tuple:
        return ("not", self.arg._key())

    def canonical(self) -> Any:
        return ["not", self.arg.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.arg,)


LOGIC_OPS = ("and", "or", "implies", "iff")


@dataclass(frozen=True, eq=False, repr=False)
class Logic(Expr):
    op: str
    lhs: Expr
    rhs: Expr
    sort: Sort = Prop

    def _key(self) -> tuple:
        return ("logic", self.op, self.lhs._key(), self.rhs._key())

    def canonical(self) -> Any:
        return [self.op, self.lhs.canonical(), self.rhs.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.lhs, self.rhs)


@dataclass(frozen=True, eq=False, repr=False)
class Quant(Expr):
    kind: str  # "forall" | "exists"
    vars: tuple[Var, ...]
    body: Expr
    sort: Sort = Prop

    def _key(self) -> tuple:
        return ("quant", self.kind, tuple(v.uid for v in self.vars), self.body._key())

    def canonical(self) -> Any:
        return [self.kind, [v.canonical() for v in self.vars], self.body.canonical()]

    def children(self) -> tuple[Expr, ...]:
        return (self.body,)


# =====================================================================================
# Literal handling and sort unification
# =====================================================================================


def _to_fraction(value: object) -> Fraction:
    if isinstance(value, bool):
        raise LiteralError("Python bool is not a mathematical literal; use pl.TRUE / pl.FALSE")
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, Fraction):
        return value
    if isinstance(value, float):
        raise LiteralError(
            f"Python float {value!r} is a binary approximation and is not accepted as an exact "
            "literal; use pl.real('0.1') or pl.rat(1, 10)"
        )
    raise LiteralError(f"cannot use {type(value).__name__} {value!r} as a mathematical literal")


def _check_literal_fits(value: Fraction, sort: Sort) -> None:
    if not sort.numeric:
        raise SortError(f"numeric literal {value} cannot have sort {sort.name}")
    if value.denominator != 1 and not sort.allows_fractions:
        raise SortError(f"fractional literal {value} is not a {sort.name}; use pl.Rat or pl.Real")
    if value < 0 and sort is Nat:
        raise SortError(f"negative literal {value} is not a Nat")


def _lift(value: object) -> Expr:
    if isinstance(value, Expr):
        return value
    return Lit(_to_fraction(value))


def _with_sort(e: Expr, sort: Sort) -> Expr:
    """Assign ``sort`` to an untyped numeral subtree (rebuilding it)."""
    if e.sort is not None:
        return e
    if isinstance(e, Lit):
        return Lit(e.value, sort)
    if isinstance(e, Neg):
        if not sort.allows_negation:
            raise SortError("unary minus is not available on Nat")
        return Neg(_with_sort(e.arg, sort), sort)
    if isinstance(e, BinOp):
        if e.op == "pow":
            return BinOp("pow", _with_sort(e.lhs, sort), e.rhs, sort)
        _check_op_allowed(e.op, sort)
        return BinOp(e.op, _with_sort(e.lhs, sort), _with_sort(e.rhs, sort), sort)
    raise SortError(f"cannot assign sort {sort.name} to {type(e).__name__}")  # pragma: no cover


def _as_numeric_term(value: object, what: str) -> Expr:
    e = _lift(value)
    if e.sort is not None and not e.sort.numeric:
        raise SortError(f"{what} needs a numeric term, got a {e.sort.name}: {_safe_text(e)}")
    return e


def _unify(a: object, b: object, what: str) -> tuple[Expr, Expr, Sort | None]:
    ea, eb = _as_numeric_term(a, what), _as_numeric_term(b, what)
    sa, sb = ea.sort, eb.sort
    if sa is None and sb is None:
        return ea, eb, None
    if sa is None:
        return _with_sort(ea, sb), eb, sb  # type: ignore[arg-type]
    if sb is None:
        return ea, _with_sort(eb, sa), sa
    if sa is not sb:
        target = sb.name if sa.rank < sb.rank else sa.name
        raise SortError(
            f"{what}: sorts differ ({sa.name} vs {sb.name}) in {_safe_text(ea)} and "
            f"{_safe_text(eb)}. PyLeanX never coerces implicitly; use pl.cast(e, pl.{target})"
        )
    return ea, eb, sa


def _coerce_to(value: object, sort: Sort, what: str) -> Expr:
    e = _lift(value)
    if e.sort is None:
        return _with_sort(e, sort)
    if e.sort is not sort:
        raise SortError(f"{what}: expected {sort.name}, got {e.sort.name} ({_safe_text(e)})")
    return e


def _check_op_allowed(op: str, sort: Sort) -> None:
    if op == "mod" and sort not in (Nat, Int):
        raise SortError(f"% is only supported on Nat and Int, not {sort.name}")


def _arith(op: str, a: object, b: object) -> Expr:
    ea, eb, sort = _unify(a, b, f"operator {op}")
    if sort is not None:
        _check_op_allowed(op, sort)
    return BinOp(op, ea, eb, sort)


def _floordiv(a: object, b: object) -> Expr:
    ea, eb, sort = _unify(a, b, "operator //")
    if sort is not None and sort not in (Nat, Int):
        raise SortError(
            "// is floor division and is only supported on Nat and Int (where Lean's `/` "
            "already rounds); use / for Rat and Real"
        )
    return BinOp("div", ea, eb, sort)


def _mod(a: object, b: object) -> Expr:
    return _arith("mod", a, b)


def _pow(base: object, exponent: object) -> Expr:
    eb = _as_numeric_term(base, "operator **")
    ee = _lift(exponent)
    if isinstance(ee, Lit) and ee.sort is None:
        ee = Lit(ee.value, Nat)  # raises for negative / fractional exponents
    if ee.sort is not Nat:
        raise SortError(
            "exponents must be natural numbers (Lean's Monoid.npow); got "
            f"{ee.sort.name if ee.sort else 'untyped'} exponent {_safe_text(ee)}"
        )
    return BinOp("pow", eb, ee, eb.sort)


def _compare(op: str, a: object, b: object) -> Compare:
    ea, eb = _lift(a), _lift(b)
    if ea.is_prop or eb.is_prop:
        raise SortError(
            "comparison between propositions is not supported; use pl.Iff(p, q) for "
            "logical equivalence"
        )
    structured = [e.sort for e in (ea, eb) if e.sort is not None and not e.sort.numeric]
    if structured:
        # Points and other non-numeric sorts: only = and ≠, between the same sort.
        if ea.sort is not eb.sort:
            raise SortError(
                f"comparison {op}: sorts differ "
                f"({ea.sort.name if ea.sort else 'numeral'} vs "
                f"{eb.sort.name if eb.sort else 'numeral'})"
            )
        if op not in ("eq", "ne"):
            raise SortError(f"ordering ({op}) is not defined on {structured[0].name}")
        return Compare(op, ea, eb)
    ea, eb, sort = _unify(ea, eb, f"comparison {op}")
    if sort is None:
        raise SortError(
            f"cannot infer the sort of {_safe_text(ea)} {op} {_safe_text(eb)}: both sides are "
            "untyped literals. Use pl.nat/pl.integer/pl.rat(.., sort=)/pl.real to fix a sort"
        )
    if op in ("lt", "le", "gt", "ge") and not sort.numeric:  # pragma: no cover - guarded above
        raise SortError(f"ordering on {sort.name} is not supported")
    return Compare(op, ea, eb)


# =====================================================================================
# Public constructors
# =====================================================================================


def _as_prop(value: object, what: str) -> Expr:
    if isinstance(value, bool):
        raise LiteralError(f"{what}: Python bool is not a proposition; use pl.TRUE / pl.FALSE")
    if not isinstance(value, Expr):
        raise SortError(f"{what} expects propositions, got {type(value).__name__}")
    if not value.is_prop:
        raise SortError(
            f"{what} expects propositions, got a term of sort "
            f"{value.sort.name if value.sort else 'numeral'}: {_safe_text(value)}"
        )
    return value


def Eq(lhs: object, rhs: object) -> Compare:  # noqa: N802 - mathematical naming
    return _compare("eq", lhs, rhs)


def Ne(lhs: object, rhs: object) -> Compare:  # noqa: N802
    return _compare("ne", lhs, rhs)


# Python reflects ``0 <= x`` to ``x >= 0``. These keep the written orientation, which
# matters when a hypothesis must match a Mathlib lemma syntactically.
def Le(lhs: object, rhs: object) -> Compare:  # noqa: N802
    return _compare("le", lhs, rhs)


def Lt(lhs: object, rhs: object) -> Compare:  # noqa: N802
    return _compare("lt", lhs, rhs)


def Ge(lhs: object, rhs: object) -> Compare:  # noqa: N802
    return _compare("ge", lhs, rhs)


def Gt(lhs: object, rhs: object) -> Compare:  # noqa: N802
    return _compare("gt", lhs, rhs)


def Not(p: object) -> NotP:  # noqa: N802
    return NotP(_as_prop(p, "Not"))


def _fold_right(op: str, props: Sequence[object]) -> Expr:
    if len(props) < 2:
        raise SortError(f"{op} needs at least two propositions")
    ps = [_as_prop(p, op.capitalize()) for p in props]
    acc = ps[-1]
    for p in reversed(ps[:-1]):
        acc = Logic(op, p, acc)
    return acc


def And(*props: object) -> Expr:  # noqa: N802
    """Conjunction (right-nested, matching Lean's right-associative ``∧``)."""
    return _fold_right("and", props)


def Or(*props: object) -> Expr:  # noqa: N802
    return _fold_right("or", props)


def Implies(*props: object) -> Expr:  # noqa: N802
    """``Implies(a, b, c)`` is ``a → b → c``."""
    return _fold_right("implies", props)


def Iff(p: object, q: object) -> Logic:  # noqa: N802
    return Logic("iff", _as_prop(p, "Iff"), _as_prop(q, "Iff"))


def _quant(kind: str, variables: Var | Iterable[Var], body: object) -> Quant:
    vs = (variables,) if isinstance(variables, Var) else tuple(variables)
    if not vs:
        raise SortError(f"{kind} needs at least one bound variable")
    seen: set[int] = set()
    for v in vs:
        if not isinstance(v, Var):
            raise SortError(f"{kind} binds variables created with pl.symbol(s), got {v!r}")
        if v.uid in seen:
            raise ScopeError(f"variable {v.name} is bound twice in the same {kind}")
        seen.add(v.uid)
    return Quant(kind, vs, _as_prop(body, kind.capitalize()))


def Forall(variables: Var | Iterable[Var], body: object) -> Quant:  # noqa: N802
    return _quant("forall", variables, body)


def Exists(variables: Var | Iterable[Var], body: object) -> Quant:  # noqa: N802
    return _quant("exists", variables, body)


def cast(e: object, sort: Sort) -> Expr:
    """Explicit embedding Nat -> Int -> Rat -> Real."""
    ex = _lift(e)
    if ex.sort is None:
        return _with_sort(ex, sort)
    if ex.sort is sort:
        return ex
    if not can_cast(ex.sort, sort):
        raise SortError(
            f"cannot cast {ex.sort.name} to {sort.name}: only Nat -> Int -> Rat -> Real "
            "embeddings are supported"
        )
    return Cast(ex, sort)


def _lit(value: object, sort: Sort) -> Lit:
    if isinstance(value, str):
        try:
            frac = Fraction(value)
        except (ValueError, ZeroDivisionError) as exc:
            raise LiteralError(f"cannot parse exact literal {value!r}") from exc
    else:
        frac = _to_fraction(value)
    return Lit(frac, sort)


def nat(value: int) -> Lit:
    return _lit(value, Nat)


def integer(value: int) -> Lit:
    return _lit(value, Int)


def real(value: int | str | Fraction) -> Lit:
    """Exact real literal; strings such as ``"0.1"`` are parsed exactly (1/10)."""
    return _lit(value, Real)


def rat(numerator: int | str | Fraction, denominator: int = 1, sort: Sort | None = None) -> Lit:
    """Exact fraction ``numerator/denominator``; untyped unless ``sort`` is given."""
    if isinstance(numerator, (float, bool)) or isinstance(denominator, (float, bool)):
        raise LiteralError("pl.rat does not accept floats/bools; pass ints or a decimal string")
    if denominator == 0:
        raise LiteralError("pl.rat: zero denominator")
    return Lit(Fraction(numerator) / Fraction(denominator), sort)


# Trusted function constants. Import modules are verified by integration tests.
_SQRT = Func("Real.sqrt", (Real,), Real, ("Mathlib.Analysis.Real.Sqrt",))
_EXP = Func("Real.exp", (Real,), Real, ("Mathlib.Analysis.SpecialFunctions.Exp",))
_LOG = Func("Real.log", (Real,), Real, ("Mathlib.Analysis.SpecialFunctions.Log.Basic",))


def sqrt(x: object) -> App:
    return _SQRT(x)


def exp(x: object) -> App:
    return _EXP(x)


def log(x: object) -> App:
    return _LOG(x)


def _unary_poly(name: str, x: object) -> App:
    e = _as_numeric_term(x, name)
    if e.sort is None:
        raise SortError(f"{name}: cannot infer the sort of an untyped literal")
    if name == "abs" and e.sort is Nat:
        raise SortError("abs is not defined for Nat in PyLeanX; cast to Int first")
    imports = ("Mathlib.Algebra.Order.Group.Unbundled.Abs",) if name == "abs" else ()
    return Func(name, (e.sort,), e.sort, imports)(e)


def _binary_poly(name: str, a: object, b: object) -> App:
    ea, eb, sort = _unify(a, b, name)
    if sort is None:
        raise SortError(f"{name}: cannot infer the sort of untyped literals")
    return Func(name, (sort, sort), sort, ("Mathlib.Order.MinMax",))(ea, eb)


def abs_(x: object) -> App:
    return _unary_poly("abs", x)


def min_(a: object, b: object) -> App:
    return _binary_poly("min", a, b)


def max_(a: object, b: object) -> App:
    return _binary_poly("max", a, b)


def make_var(name: str, sort: Sort, origin: Origin | None = None) -> Var:
    if not isinstance(sort, Sort):
        raise SortError(
            f"sort must be a pl.Sort (pl.Nat, pl.Int, pl.Rat, pl.Real, pl.Prop, "
            f"pl.geometry.Point, ...), got {sort!r}"
        )
    validate_identifier(name, "variable name")
    return Var(name, sort, origin=origin or caller_origin())


def iter_subexprs(e: Expr) -> Iterable[Expr]:
    stack = [e]
    while stack:
        cur = stack.pop()
        yield cur
        stack.extend(reversed(cur.children()))


__all__ = [
    "Expr", "Var", "Lit", "PropConst", "TRUE", "FALSE", "BinOp", "Neg", "Cast", "Func", "App",
    "Compare", "NotP", "Logic", "Quant", "Eq", "Ne", "Le", "Lt", "Ge", "Gt", "Not", "And", "Or",
    "Implies", "Iff",
    "Forall", "Exists", "cast", "nat", "integer", "real", "rat", "sqrt", "exp", "log",
    "abs_", "min_", "max_", "make_var", "iter_subexprs",
]

import pytest

import pyleanx as pl
from pyleanx.expr import BinOp, Compare, Lit


@pytest.fixture
def xy():
    return pl.symbols("x y", pl.Real)


def test_operators_build_ir(xy):
    x, y = xy
    e = x + 2 * y
    assert isinstance(e, BinOp) and e.op == "add" and e.sort is pl.Real
    assert isinstance(e.rhs.lhs, Lit) and e.rhs.lhs.sort is pl.Real  # literal took context sort


def test_eq_returns_proposition(xy):
    x, y = xy
    p = x == y
    assert isinstance(p, Compare) and p.is_prop and p.op == "eq"
    assert (x != y).op == "ne"


def test_bool_raises(xy):
    x, _ = xy
    with pytest.raises(pl.SymbolicTruthValueError):
        if x == 0:
            pass
    with pytest.raises(pl.SymbolicTruthValueError):
        bool(x)


def test_python_logic_keywords_rejected(xy):
    x, y = xy
    with pytest.raises(pl.SymbolicTruthValueError):
        (x > 0) and (y > 0)  # noqa: B015
    with pytest.raises(pl.SymbolicTruthValueError):
        not (x > 0)  # noqa: B015
    with pytest.raises(pl.SymbolicTruthValueError):
        0 <= x <= 1  # noqa: B015 - chained comparison


def test_unhashable(xy):
    x, _ = xy
    with pytest.raises(TypeError):
        {x: 1}  # noqa: B018
    with pytest.raises(TypeError):
        {x}  # noqa: B018


def test_no_float_or_index(xy):
    x, _ = xy
    with pytest.raises(TypeError):
        float(x)
    with pytest.raises(TypeError):
        range(x)


def test_float_and_bool_literals_rejected(xy):
    x, _ = xy
    with pytest.raises(pl.LiteralError):
        x + 0.5
    with pytest.raises(pl.LiteralError):
        x == True  # noqa: E712


def test_no_implicit_coercion(xy):
    x, _ = xy
    n = pl.symbol("n", pl.Nat)
    with pytest.raises(pl.SortError):
        n + x
    assert (pl.cast(n, pl.Real) + x).sort is pl.Real
    with pytest.raises(pl.SortError):
        pl.cast(x, pl.Nat)
    assert pl.cast(x, pl.Real) is x


def test_nat_restrictions():
    n = pl.symbol("n", pl.Nat)
    with pytest.raises(pl.SortError):
        -n
    with pytest.raises(pl.SortError):
        n + pl.rat(1, 2)
    assert (n - 1).sort is pl.Nat  # truncated subtraction is Lean semantics; allowed
    assert (n // 2).op == "div" and (n % 2).op == "mod"


def test_floordiv_and_mod_only_on_integers(xy):
    x, _ = xy
    with pytest.raises(pl.SortError):
        x // 2
    with pytest.raises(pl.SortError):
        x % 2


def test_pow_requires_nat_exponent(xy):
    x, _ = xy
    assert (x**2).rhs.sort is pl.Nat
    with pytest.raises(pl.SortError):
        x ** -1
    with pytest.raises(pl.SortError):
        x**x
    k = pl.symbol("k", pl.Nat)
    assert (x**k).sort is pl.Real


def test_untyped_literal_comparison_rejected():
    with pytest.raises(pl.SortError):
        pl.rat(1, 2) < 1
    assert (pl.real(2) + 2 == 4).lhs.sort is pl.Real


def test_untyped_literal_tree_gets_sort(xy):
    x, _ = xy
    e = x + (pl.rat(1, 2) + pl.rat(1, 3))
    assert e.rhs.sort is pl.Real and e.rhs.lhs.sort is pl.Real


def test_prop_connectives(xy):
    x, y = xy
    P, Q = pl.prop_symbol("P"), pl.prop_symbol("Q")
    assert (P & Q).op == "and" and (P | Q).op == "or" and (~P).arg is P
    assert pl.And(P, Q, x > 0).rhs.op == "and"  # right nested
    with pytest.raises(pl.SortError):
        pl.And(P)
    with pytest.raises(pl.SortError):
        pl.Not(x)
    with pytest.raises(pl.SortError):
        P == Q  # use Iff
    with pytest.raises(pl.SortError):
        x & y
    assert pl.Iff(P, Q).op == "iff"


def test_same_structure(xy):
    x, y = xy
    assert (x + y).same_structure(x + y)
    assert not (x + y).same_structure(y + x)
    x2 = pl.symbol("x", pl.Real)  # same name, different variable
    assert not (x + 1).same_structure(x2 + 1)
    assert not x.same_structure(1)  # type: ignore[arg-type]


def test_canonical_is_name_based(xy):
    x, _ = xy
    assert (x + 1).canonical() == ["add", ["var", "x", "Real"], ["lit", "1", "Real"]]


def test_functions(xy):
    x, _ = xy
    assert pl.sqrt(x).sort is pl.Real
    assert abs(x).func.lean_name == "abs"
    with pytest.raises(pl.SortError):
        pl.sqrt(pl.symbol("n", pl.Nat))
    with pytest.raises(pl.SortError):
        abs(pl.symbol("n", pl.Nat))
    with pytest.raises(pl.SymbolicTruthValueError):
        max(x, 1)  # builtin max needs truth values
    assert pl.max(x, 1).func.lean_name == "max"
    with pytest.raises(pl.SortError):
        pl.Func("Real.sqrt", (pl.Real,), pl.Real)(x, x)


def test_quantifiers(xy):
    x, y = xy
    q = pl.Forall([x], pl.Exists(y, y > x))
    assert q.kind == "forall" and q.body.kind == "exists"
    with pytest.raises(pl.ScopeError):
        pl.Forall([x, x], x > 0)
    with pytest.raises(pl.SortError):
        pl.Forall([], x > 0)
    with pytest.raises(pl.SortError):
        pl.Forall([x], x + 1)


def test_repr_never_fails(xy):
    x, y = xy
    assert "x + y" in repr(x + y)
    assert str(x * y) == "x * y"

import pytest

import pyleanx as pl


def test_undeclared_variable():
    x, y = pl.symbols("x y", pl.Real)
    with pytest.raises(pl.ScopeError, match="'y' is not declared"):
        pl.Theorem("t", variables=[x], conclusion=x + y == y + x)


def test_same_name_different_variable():
    x = pl.symbol("x", pl.Real)
    x_other = pl.symbol("x", pl.Real)
    with pytest.raises(pl.ScopeError, match="different variable"):
        pl.Theorem("t", variables=[x], conclusion=x_other > 0)
    with pytest.raises(pl.ScopeError, match="declared twice"):
        pl.Theorem("t", variables=[x, x_other], conclusion=x > 0)
    with pytest.raises(pl.ScopeError, match="listed twice"):
        pl.Theorem("t", variables=[x, x], conclusion=x > 0)


def test_quantifier_capture_rejected():
    x = pl.symbol("x", pl.Real)
    x_inner = pl.symbol("x", pl.Real)
    with pytest.raises(pl.ScopeError, match="shadows"):
        pl.Theorem("t", variables=[x], conclusion=pl.Forall([x_inner], x_inner > x))
    with pytest.raises(pl.ScopeError, match="rebinds"):
        pl.Theorem("t", variables=[x], conclusion=pl.Forall([x], x > 0))


def test_bound_variables_ok_and_free_vars():
    x, y = pl.symbols("x y", pl.Real)
    p = pl.Forall([x], pl.Exists([y], y > x))
    pl.Theorem("t", conclusion=p)  # closed statement
    assert pl.free_vars(p) == []
    assert [v.name for v in pl.free_vars(pl.Exists([y], y > x))] == ["x"]


def test_hypothesis_names():
    x = pl.symbol("x", pl.Real)
    with pytest.raises(pl.ScopeError):
        pl.Theorem("t", [x], assumptions=[("x", x > 0)], conclusion=x > 0)
    with pytest.raises(pl.ScopeError):
        pl.Theorem("t", [x], assumptions=[("h", x > 0), ("h", x > 1)], conclusion=x > 0)
    t = pl.Theorem("t", [x], assumptions=[x > 0, x > 1], conclusion=x > 0)
    assert [h.name for h in t.assumptions] == ["h1", "h2"]
    t2 = pl.Theorem("t2", [x], assumptions={"hpos": x > 0}, conclusion=x > 0)
    assert t2.assumptions[0].name == "hpos"
    with pytest.raises(pl.SortError):
        pl.Theorem("t3", [x], assumptions=[x + 1], conclusion=x > 0)
    with pytest.raises(pl.ScopeError):
        y = pl.symbol("y", pl.Real)
        pl.Theorem("t4", [x], assumptions=[("h", y > 0)], conclusion=x > 0)


@pytest.mark.parametrize(
    "name",
    ["bad name", "x\ntheorem evil", "a.b", "theorem", "sorry", "1abc", "", "x;y", "Real", "ℝ"],
)
def test_illegal_identifiers(name):
    with pytest.raises(pl.IdentifierError):
        pl.symbol(name, pl.Real)


@pytest.mark.parametrize("name", ["evil :\n  sorry\naxiom", "t t", "axiom", "a.b"])
def test_illegal_theorem_names(name):
    x = pl.symbol("x", pl.Real)
    with pytest.raises(pl.IdentifierError):
        pl.Theorem(name, [x], conclusion=x == x)


def test_conclusion_must_be_prop():
    x = pl.symbol("x", pl.Real)
    with pytest.raises(pl.SortError):
        pl.Theorem("t", [x], conclusion=x + 1)
    with pytest.raises(pl.SortError):
        pl.Theorem("t", [x])


def test_bad_sort_argument():
    with pytest.raises(pl.SortError):
        pl.symbol("x", float)  # type: ignore[arg-type]

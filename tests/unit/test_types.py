from fractions import Fraction

import pytest

import pyleanx as pl
from pyleanx.types import can_cast


def test_sorts_are_descriptors():
    assert pl.Real.lean == "Real" and pl.Nat.lean == "Nat" and pl.Prop.is_prop
    assert repr(pl.Int) == "pl.Int"


def test_cast_chain_only_upwards():
    assert can_cast(pl.Nat, pl.Real) and can_cast(pl.Int, pl.Rat)
    assert not can_cast(pl.Real, pl.Nat) and not can_cast(pl.Prop, pl.Real)


def test_literal_constructors():
    assert pl.real("0.1").value == Fraction(1, 10)
    assert pl.rat(2, 3).value == Fraction(2, 3) and pl.rat(2, 3).sort is None
    assert pl.integer(-3).sort is pl.Int


@pytest.mark.parametrize(
    "bad",
    [lambda: pl.nat(-1), lambda: pl.nat(Fraction(1, 2)), lambda: pl.integer(Fraction(1, 2))],
)
def test_literal_must_fit_sort(bad):
    with pytest.raises(pl.SortError):
        bad()


@pytest.mark.parametrize(
    "bad",
    [lambda: pl.real(0.1), lambda: pl.rat(0.5), lambda: pl.rat(1, 0), lambda: pl.real("abc"),
     lambda: pl.nat(True)],
)
def test_inexact_literals_rejected(bad):
    with pytest.raises(pl.LiteralError):
        bad()

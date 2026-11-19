"""Statement operations (pyleanx.ops), no Lean."""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import geometry as geo
from pyleanx import ops

x, y = pl.symbols("x y", pl.Real)
A, B, C = geo.points("A B C")


def test_substitute_takes_variables_and_numbers_and_respects_binders():
    e = x + 2 * y
    assert ops.same(ops.substitute(e, (x, 0)), pl.real(0) + 2 * y)
    bound = pl.Forall(x, x + y > 0)
    assert ops.same(ops.substitute(bound, (x, 1)), bound)       # x is bound there
    with pytest.raises(TypeError, match="pairs"):
        ops.substitute(e, ("x", 0))


def test_exchange_swaps_simultaneously():
    e = geo.dist(A, C) ** 2 == geo.dist(A, B) * geo.dist(B, C)
    swapped = ops.exchange(e, (A, B))
    assert ops.same(swapped, geo.dist(B, C) ** 2 == geo.dist(B, A) * geo.dist(A, C))
    assert ops.same(ops.exchange(swapped, (A, B)), e)
    with pytest.raises(TypeError, match="pairs of variables"):
        ops.exchange(e, (A,))


def test_free_vars_sorts_and_symbols():
    e = pl.Forall(y, geo.angle(A, B, C) + y > x)
    assert [v.name for v in ops.free_vars(e)] == ["A", "B", "C", "x"]
    assert {"Point", "Real"} <= ops.sorts(e)
    assert ops.symbols(e) == {"EuclideanGeometry.angle"}
    assert len(list(ops.subterms(x + y))) == 3


def test_vocabulary_of_a_theorem_activates_its_packs():
    from pyleanx.render.lean import theorem_packs

    tri = pl.Theorem("t", [A, B, C], conclusion=geo.dist(A, B) == geo.dist(B, A),
                     proof=pl.proof(pl.conclude()))
    num = pl.Theorem("n", [x], conclusion=x + 0 == x, proof=pl.proof(pl.conclude()))
    assert "Point" in ops.vocabulary(tri)[0]
    assert "geometry" in theorem_packs(tri) and "geometry" not in theorem_packs(num)
    assert "angle_comm" in tri.to_lean() and "angle_comm" not in num.to_lean()

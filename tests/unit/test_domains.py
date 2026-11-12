"""M6 domain modules: typing rules, rendering, catalogs (no Lean needed)."""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import algebra as alg
from pyleanx import analysis as an
from pyleanx import geometry as geo
from pyleanx._domain import VERIFIED_MATHLIB, all_catalogs, catalog_status
from pyleanx.proofs import Name


def test_points_render_as_plane_binders():
    A, B, C = geo.points("A B C")
    thm = pl.Theorem("t", [A, B, C], conclusion=geo.dist(A, C) <= geo.dist(A, B) + geo.dist(B, C),
                     proof=pl.exact(geo.dist_triangle(A, B, C)))
    src = thm.to_lean(audit=False)
    assert "theorem t (A B C : EuclideanSpace Real (Fin 2)) :" in src
    assert "dist A C ≤ dist A B + dist B C" in src
    assert "exact dist_triangle A B C" in src
    assert "import Mathlib.Analysis.InnerProductSpace.PiL2" in src


def test_point_equality_and_disequality_only():
    A, B = geo.points("A B")
    assert (A != B).to_lean() == "A ≠ B"
    assert pl.Eq(A, B).to_lean() == "A = B"
    with pytest.raises(pl.SortError, match="ordering"):
        A < B
    with pytest.raises(pl.SortError):
        A + B
    with pytest.raises(pl.SortError):
        A == 0
    x = pl.symbol("x", pl.Real)
    with pytest.raises(pl.SortError, match="sorts differ"):
        A == x


def test_geometry_functions_check_argument_sorts():
    A, B = geo.points("A B")
    x = pl.symbol("x", pl.Real)
    with pytest.raises(pl.SortError):
        geo.dist(A, x)
    with pytest.raises(pl.SortError):
        geo.angle(A, B, 1)
    assert geo.angle(A, B, A).sort is pl.Real


def test_pi_constant_and_trig_render():
    x = pl.symbol("x", pl.Real)
    assert (pl.pi() / 2).to_lean() == "Real.pi / 2"
    assert (an.sin(x)**2 + an.cos(x)**2 == 1).to_lean() == "Real.sin x ^ 2 + Real.cos x ^ 2 = 1"
    assert an.sin(x + 1).to_lean() == "Real.sin (x + 1)"


def test_latex_templates():
    A, B, C = geo.points("A B C")
    assert geo.angle(A, B, C).to_latex() == r"\angle ABC"
    assert geo.dist(A, B).to_latex() == r"\lvert AB \rvert"
    assert pl.pi().to_latex() == r"\pi"
    x = pl.symbol("x", pl.Real)
    assert an.sin(x).to_latex() == r"\sin x"
    assert r"\sin" in an.sin(x + 1).to_latex()
    assert r"\mathbb{R}^2" in pl.Theorem("t", [A], conclusion=A == A).to_latex()


def test_ordered_constructors_keep_orientation():
    x = pl.symbol("x", pl.Real)
    assert (0 <= x).to_lean() == "x ≥ 0"  # Python reflects this
    assert pl.Le(0, x).to_lean() == "0 ≤ x"
    assert pl.Lt(0, x).to_lean() == "0 < x"
    assert pl.Ge(x, 1).to_lean() == "x ≥ 1"
    assert pl.Gt(x, 1).to_lean() == "x > 1"


def test_algebra_helpers_build_proofs():
    a, b = pl.symbols("a b", pl.Real)
    t = alg.identity("sq", (a + b)**2, a**2 + 2*a*b + b**2)
    assert [v.name for v in t.variables] == ["a", "b"]
    assert "  ring" in t.to_lean()
    t2 = alg.am_gm_two("amgm", a, b)
    assert "2 * a * b ≤ a ^ 2 + b ^ 2" in t2.to_lean()
    assert "nlinarith [sq_nonneg (a - b)]" in t2.to_lean()
    t3 = alg.nonneg("nn", (a - b)**2)
    assert "0 ≤ (a - b) ^ 2" in t3.to_lean() and "positivity" in t3.to_lean()
    t4 = alg.inequality("ineq", a, "<", a + 1, proof=pl.linarith())
    assert "a < a + 1" in t4.to_lean()
    with pytest.raises(pl.SortError):
        alg.inequality("bad", a, "!=", b)


def test_inequality_collects_variables_from_assumptions():
    a, b = pl.symbols("a b", pl.Real)
    t = alg.inequality("t", a, "<=", a + b, assumptions={"hb": pl.Le(0, b)})
    assert [v.name for v in t.variables] == ["a", "b"]


def test_catalogs_are_named_references_with_imports():
    cats = all_catalogs()
    assert set(cats) == {"mathlib", "algebra", "analysis", "geometry", "numbers",
                         "complex_analysis"}
    total = 0
    for cat in cats.values():
        for key, ref in cat.items():
            assert isinstance(ref, Name), key
            total += 1
    assert total >= 50
    assert "add_pos" not in alg.LEMMAS  # misleading name at the pinned revision
    assert geo.LEMMAS["pythagoras_iff"].name.endswith("iff_angle_eq_pi_div_two")


def test_catalog_status_flags_other_mathlib_revisions():
    assert catalog_status(VERIFIED_MATHLIB) == "ok"
    assert "lemma names may differ" in catalog_status("0" * 40)

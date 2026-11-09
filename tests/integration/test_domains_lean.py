"""M6 gate: domain modules prove algebra, analysis and plane-geometry statements with
pinned Mathlib facts (real Lean + axiom audit)."""

from __future__ import annotations

import os

import pytest

import pyleanx as pl
from pyleanx import algebra as alg
from pyleanx import analysis as an
from pyleanx import geometry as geo

pytestmark = pytest.mark.lean


def _gate_theorems() -> list[pl.Theorem]:
    a, b = pl.symbols("a b", pl.Real)
    x = pl.symbol("x", pl.Real)
    A, B, C = geo.points("A B C")
    return [
        alg.identity("m6_poly_identity", (a + b)**2, a**2 + 2*a*b + b**2),
        alg.nonneg("m6_square_nonneg", (a - b)**2),
        alg.am_gm_two("m6_am_gm", a, b),
        pl.Theorem("m6_trig", [x], conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
                   proof=pl.exact(an.sin_sq_add_cos_sq(x))),
        pl.Theorem("m6_sqrt_sq", [x], assumptions={"hx": pl.Le(0, x)},
                   conclusion=an.sqrt(x)**2 == x, proof=pl.exact(an.sq_sqrt("hx"))),
        pl.Theorem("m6_triangle_ineq", [A, B, C],
                   conclusion=geo.dist(A, C) <= geo.dist(A, B) + geo.dist(B, C),
                   proof=pl.exact(geo.dist_triangle(A, B, C))),
        pl.Theorem("m6_angle_sum", [A, B, C], assumptions={"h": B != A},
                   conclusion=geo.angle(A, B, C) + geo.angle(B, C, A) + geo.angle(C, A, B)
                   == pl.pi(),
                   proof=pl.exact(geo.angle_add_angle_add_angle_eq_pi(C, pl.hyp("h")))),
        pl.Theorem("m6_pythagoras", [A, B, C],
                   assumptions={"h": geo.angle(A, B, C) == pl.pi() / 2},
                   conclusion=geo.dist(A, C) * geo.dist(A, C)
                   == geo.dist(A, B) * geo.dist(A, B) + geo.dist(C, B) * geo.dist(C, B),
                   proof=pl.rw(geo.pythagoras_iff) >> pl.exact("h")),
    ]


def test_m6_gate_domain_examples_verify(lean_project):
    results = pl.verify_all(_gate_theorems(), project=lean_project, use_cache=False,
                           timeout=1800)
    for r in results:
        assert r.status is pl.Status.VERIFIED, r.summary() + "\n" + r.lean_source
        assert "sorryAx" not in (r.axioms or ())


def test_m6_false_geometry_claim_rejected(lean_project):
    A, B, C = geo.points("A B C")
    bad = pl.Theorem("m6_bad_triangle", [A, B, C],
                     conclusion=geo.dist(A, B) + geo.dist(B, C) <= geo.dist(A, C),
                     proof=pl.exact(geo.dist_triangle(A, B, C)))
    r = bad.verify(lean_project, use_cache=False, timeout=1800)
    assert r.status is pl.Status.REJECTED


@pytest.mark.skipif(os.environ.get("PYLEANX_SLOW_TESTS") != "1",
                    reason="checks every catalog name (~10 min here); set PYLEANX_SLOW_TESTS=1")
def test_every_catalog_name_exists_in_pinned_mathlib(lean_project):
    from pyleanx._domain import all_catalogs
    from pyleanx.backend.declarations import check_declarations

    names, imports = [], set()
    for cat in all_catalogs().values():
        for ref in cat.values():
            names.append(ref.name)
            imports.update(ref.imports)
    infos = check_declarations(names, imports, lean_project, timeout=1800)
    missing = {n: i.error for n, i in infos.items() if not i.exists}
    assert not missing, missing

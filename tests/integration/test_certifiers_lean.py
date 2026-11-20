"""Certificates checked by real Lean through verify(): proved, audited, never trusted.

Each theorem here is one the justification rules alone do not prove under Lean's default
budget (benchmarks/certificates.py); with pyleanx.certifiers they verify, and their axioms
are the standard three. A certifier proposing a wrong certificate for a false step can
never make it verified.
"""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import justify
from pyleanx import numbers as nt

pytestmark = pytest.mark.lean
pytest.importorskip("sympy")
pytest.importorskip("scipy")


@pytest.fixture
def certifiers():
    import pyleanx.certifiers as c

    c.enable()
    try:
        yield c
    finally:
        c.disable()


def _one(name, vs, hyps, goal):
    return pl.Theorem(name, vs, assumptions=hyps, conclusion=goal, proof=pl.proof(
        pl.claim(goal, because=list(hyps), name="h"), pl.conclude(because="h")))


def test_certified_steps_verify_across_domains(lean_project, certifiers):
    a, b, c, x, y = pl.symbols("a b c x y", pl.Real)
    m, n = pl.symbols("m n", pl.Int)
    theorems = [
        _one("cert_am_gm_three", [a, b, c], {"ha": a >= 0, "hb": b >= 0, "hc": c >= 0},
             a ** 3 + b ** 3 + c ** 3 >= 3 * a * b * c),
        _one("cert_am_hm", [x, y], {"hx": x > 0, "hy": y > 0}, x / y + y / x >= 2),
        _one("cert_exists_root", [], {}, pl.Exists(y, pl.And(y ** 2 + 2 * y == 3, y > 0))),
        _one("cert_cubes", [m, n], {}, nt.divides(m - n, m ** 3 - n ** 3)),
        pl.Theorem("cert_contradiction", [x], conclusion=x ** 2 + 2 * x + 2 > 0,
                   proof=pl.proof(pl.suppose_not(x ** 2 + 2 * x + 2 <= 0, name="hneg"),
                                  pl.conclude(because="hneg"))),
        pl.Theorem("cert_after_fix", [], conclusion=pl.Forall([a, b], pl.Implies(
            a >= 0, pl.Implies(b >= 0, a ** 3 + b ** 3 >= a ** 2 * b + a * b ** 2))),
            proof=pl.proof(pl.fix(a, b, assume={"ha": a >= 0, "hb": b >= 0}),
                           pl.conclude(because=["ha", "hb"]))),
    ]
    results = pl.verify_all(theorems, project=lean_project, use_cache=False, timeout=1800)
    for t, r in zip(theorems, results, strict=True):
        assert r.verified, (t.name, r.status, [e.message for e in r.errors][:2])
        assert set(r.axioms) <= {"propext", "Classical.choice", "Quot.sound"}


def test_a_wrong_certificate_never_verifies_a_false_step(lean_project):
    x = pl.symbol("x", pl.Real)

    def wrong(goal: justify.Goal) -> str:
        return "linear_combination (sq_nonneg x)"

    justify.register_certifier("wrong", wrong)
    try:
        r = _one("cert_false", [x], {}, x ** 2 < 0).verify(lean_project)
    finally:
        justify.unregister_certifier("wrong")
    assert not r.verified and r.status is pl.Status.REJECTED

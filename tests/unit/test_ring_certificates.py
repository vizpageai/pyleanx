"""The ring certifier: linear_combination coefficients found in Python (no Lean)."""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import justify

x, y = pl.symbols("x y", pl.Real)


def _thm(goal=None, hyps=None, name="h3") -> pl.Theorem:
    hyps = hyps or {"h1": x == 2, "h2": y == x ** 2}
    goal = goal if goal is not None else y == 4
    return pl.Theorem("t", [x, y], assumptions=hyps, conclusion=goal, proof=pl.proof(
        pl.claim(goal, because=list(hyps), name=name), pl.conclude(because=name)))


sympy = pytest.importorskip("sympy")


@pytest.fixture
def ring():
    import pyleanx.ring_certificates as rc

    justify.register_certifier(rc.NAME, rc.certify, priority=10, imports=rc.IMPORTS)
    try:
        yield rc
    finally:
        justify.unregister_certifier(rc.NAME)


def _cert(thm: pl.Theorem, step: str = "h3") -> list[str]:
    return [t for _, t in thm.derivation().certificates(step)]


def test_ring_certificates(ring):
    assert _cert(_thm()) == ["linear_combination (x + 2) * h1 + h2"]
    a, b, s, p = pl.symbols("a b s p", pl.Real)
    thm = pl.Theorem("v", [a, b, s, p], assumptions={"hs": a + b == s, "hp": a * b == p},
                     conclusion=a ** 2 + b ** 2 == s ** 2 - 2 * p, proof=pl.proof(
                         pl.claim(a ** 2 + b ** 2 == s ** 2 - 2 * p, because=["hs", "hp"],
                                  name="h"), pl.conclude(because="h")))
    assert _cert(thm, "h") == ["linear_combination (a + b + s) * hs + (-2) * hp"]


def test_ring_certificate_over_int_uses_integer_coefficients(ring):
    m, n = pl.symbols("m n", pl.Int)
    thm = pl.Theorem("i", [m, n], assumptions={"h": 2 * m == n},
                     conclusion=m == n, proof=pl.proof(
                         pl.claim(m == n, because="h", name="k"), pl.conclude(because="k")))
    assert _cert(thm, "k") == []          # m - n is not an integer multiple of 2m - n


def test_ring_certifier_declines_what_it_cannot_certify(ring):
    assert _cert(_thm(goal=y == 5)) == []                   # false: no certificate
    assert _cert(_thm(goal=y <= 4)) == []                   # not an equality
    n = pl.symbol("n", pl.Nat) if hasattr(pl, "symbol") else pl.symbols("n", pl.Nat)[0]
    thm = pl.Theorem("nat", [n], assumptions={"h": n == 2}, conclusion=n * n == 4,
                     proof=pl.proof(pl.claim(n * n == 4, because="h", name="k"),
                                    pl.conclude(because="k")))
    assert _cert(thm, "k") == []                            # ℕ: no subtraction


def test_find_coefficients_is_an_identity(ring):
    a, b, s, p = sympy.symbols("a b s p")
    gens = [a + b - s, a * b - p]
    target = sympy.expand(a ** 4 + b ** 4 - (s ** 4 - 4 * s ** 2 * p + 2 * p ** 2))
    cs = ring.find_coefficients(target, gens, [a, b, s, p], integral=False)
    assert cs is not None
    assert sympy.expand(target - sum(c * g for c, g in zip(cs, gens, strict=True))) == 0

"""The certifiers of pyleanx.certifiers (no Lean): what they propose, and that it is exact.

Every certificate is also re-checked here in Python where possible (the identity behind a
``linear_combination``); Lean's check is in benchmarks/certificates.py.
"""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import justify
from pyleanx import numbers as nt

sympy = pytest.importorskip("sympy")
try:
    import scipy  # noqa: F401
    HAVE_SCIPY = True
except ImportError:  # the exact (sympy) LP fallback finds fewer certificates
    HAVE_SCIPY = False
needs_scipy = pytest.mark.skipif(not HAVE_SCIPY, reason="large LPs need scipy (HiGHS)")


@pytest.fixture(autouse=True)
def certifiers():
    import pyleanx.certifiers as c

    c.enable()
    try:
        yield c
    finally:
        c.disable()


x, y, a, b, c, d = pl.symbols("x y a b c d", pl.Real)
m, n = pl.symbols("m n", pl.Int)
k, j = pl.symbols("k j", pl.Nat)


def certs(goal, **hyps) -> list[tuple[str, str]]:
    return justify.certificates(goal, list(hyps), hyps)


def only(goal, **hyps) -> tuple[str, str]:
    found = certs(goal, **hyps)
    assert found, f"no certificate for {goal}"
    return found[0]


# --- polynomial equalities ------------------------------------------------------------

def test_polynomial_equalities_over_every_ring():
    assert only(y == 4, h1=x == 2, h2=y == x ** 2) == \
        ("polynomial", "linear_combination (x + 2) * h1 + h2")
    assert only(m ** 2 == n ** 2 + 2 * n + 1, h=m == n + 1) == \
        ("polynomial", "linear_combination (m + n + 1) * h")
    # ℕ: coefficients split into monomials, signs outside (formal subtraction)
    assert only(k * k == j * j, h=k == j) == ("polynomial", "linear_combination k * h + j * h")


def test_non_polynomial_terms_are_atoms():
    s, co = pl.sin(x), pl.cos(x)
    assert only((s + co) ** 2 == 1 + 2 * s * co, h=s ** 2 + co ** 2 == 1) == \
        ("polynomial", "linear_combination h")


def test_no_certificate_for_a_false_or_trivial_step():
    assert certs(y == 5, h1=x == 2, h2=y == x ** 2) == []     # false
    assert certs(x + y == y + x) == []                          # ring alone
    assert certs(2 * m == n, h=m == n) == []                    # not an integer multiple


# --- inequalities ---------------------------------------------------------------------

@pytest.mark.parametrize("goal, hyps, expected", [
    (2 * a * b <= a ** 2 + b ** 2, {}, "linear_combination (sq_nonneg (a - b))"),
    pytest.param((a * c + b * d) ** 2 <= (a ** 2 + b ** 2) * (c ** 2 + d ** 2), {},
                 "linear_combination (sq_nonneg (a * d - b * c))", marks=needs_scipy),
    (x <= 3, {"h1": x + y <= 4, "h2": y >= 1}, "linear_combination h1 + (ge_iff_le.mp h2)"),
])
def test_inequality_certificates(goal, hyps, expected):
    assert only(goal, **hyps) == ("inequality", expected)


@needs_scipy
def test_am_gm_three_uses_hypotheses_times_squares():
    name, text = only(a ** 3 + b ** 3 + c ** 3 >= 3 * a * b * c, ha=a >= 0, hb=b >= 0,
                      hc=c >= 0)
    assert name == "inequality" and text.startswith("(show 3 * a * b * c ≤")
    assert "mul_nonneg (sub_nonneg.mpr (ge_iff_le.mp ha)) (sq_nonneg" in text


def test_strict_inequalities_need_a_strict_part():
    name, text = only(x ** 3 > 1, hx=x > 1)
    assert name == "inequality" and "gt_iff_lt.mp hx" in text
    assert certs(x ** 2 > 0) == []          # false at x = 0: no certificate


def test_conjunctions_are_split_and_known_nonnegative_terms_used():
    _, text = only(a * b <= 1, h=pl.And(0 <= a, a <= 1, 0 <= b, b <= 1))
    assert "h.2" in text and "mul_nonneg" in text
    _, text = only(pl.sqrt(x) + 1 > 0)
    assert "(show (0 : ℝ) ≤ Real.sqrt x by positivity)" in text


def test_a_false_inequality_has_no_certificate():
    assert certs(a ** 2 + b ** 2 <= 2 * a * b) == []
    assert certs(x <= 2, h1=x + y <= 4, h2=y >= 1) == []


def test_lp_solutions_are_exact_identities(certifiers):
    from pyleanx.certifiers import _algebra as al

    s = sympy.symbols("s")
    found = al.nonneg_combination(sympy.Integer(1) + s ** 2,
                                  [(s ** 2, False)], [], [s], strict=True, integral=False)
    assert found is not None
    lam, _, const = found
    assert lam == [1] and const == 1


# --- existence ------------------------------------------------------------------------

def test_witnesses_solved_for_then_instance_certified():
    name, text = only(pl.Exists(y, pl.And(y ** 2 + 2 * y == 3, y > 0)))
    assert name == "witness" and text.startswith("exact ⟨(1 : Real), (by first |")
    assert only(pl.Exists(y, x + y == 3))[1].startswith("exact ⟨-x + 3, ")
    _, text = only(pl.Exists(y, y > x))
    assert text.startswith("exact ⟨x + 1, (by first | (show x < x + 1; linear_combination)")


def test_no_witness_for_an_impossible_statement():
    assert certs(pl.Exists(y, pl.And(y > 1, y < 0))) == []


# --- divisibility ---------------------------------------------------------------------

def test_divisibility_quotients():
    assert only(nt.divides(m - n, m ** 3 - n ** 3)) == \
        ("divisibility", "(exact ⟨m ^ 2 + m * n + n ^ 2, by ring⟩)")
    name, text = only(nt.divides(m, 2 * n + 3 * n * n), h=nt.divides(m, n))
    assert text.startswith("(obtain ⟨pyleanx_k1, pyleanx_hk1⟩ := h; exact ⟨")
    assert only(nt.divides(k, k ** 2 + k))[1] == "(exact ⟨k + 1, by ring⟩)"


def test_no_quotient_when_none_is_polynomial():
    assert certs(nt.divides(2 * m, m ** 2)) == []


# --- the package ----------------------------------------------------------------------

def test_disable_removes_every_certifier(certifiers):
    certifiers.disable()
    assert certs(y == 4, h1=x == 2, h2=y == x ** 2) == []
    certifiers.enable()
    assert certs(y == 4, h1=x == 2, h2=y == x ** 2)


def test_certificates_in_a_written_proof():
    thm = pl.Theorem("t", [a, b], conclusion=2 * a * b <= a ** 2 + b ** 2,
                     proof=pl.proof(pl.conclude()))
    from pyleanx.render.lean import render_module

    src = render_module([thm]).source
    assert "linear_combination (sq_nonneg (a - b))" in src
    assert "import Mathlib.Tactic.LinearCombination" in src

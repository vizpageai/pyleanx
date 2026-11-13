"""Harmonic-analysis vocabulary, shipped definitions/facts and the lecture helpers (no Lean)."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

import pyleanx as pl
from pyleanx import harmonic as ha
from pyleanx.proofs import LIBRARY_FACTS, LibraryFact, library_facts

EXAMPLES = Path(__file__).resolve().parents[2] / "examples"
f, g = pl.symbols("f g", ha.CFun)
n = pl.symbol("n", pl.Int)
xi = pl.symbol("ξ", pl.Real)


def test_statements_print_as_in_the_book():
    t = pl.Theorem("t", [f, g, n, xi], assumptions={"h": ha.L2(f), "hd": ha.derivative(f, g)},
                   conclusion=pl.And(ha.coeff_sq_sum(f) == ha.mean_square(f),
                                     ha.coeffs_tend_to_zero(f), ha.ft(f, xi) == ha.gauss(xi),
                                     ha.ift(ha.ft_fun(f), xi) == f(xi)))
    text = str(t.prose())
    assert "f ∈ L²(-π, π)" in text and "f′(x) = g(x)" in text
    assert "|f̂(n)|²" in text and "f̂(n) → 0 as |n| → ∞" in text and "f̂(ξ) = e^(-π ξ²)" in text
    md = t.prose().to_markdown()
    assert r"\hat{f}(\xi)" in md and r"\frac{1}{2\pi} \int_{-\pi}^{\pi}" in md


def test_shipped_definitions_used_in_statements_are_emitted():
    t = pl.Theorem("t", [f, n], conclusion=ha.coeff(f, n) == ha.coeff(f, n),
                   proof=pl.proof(pl.conclude()))
    names = [x.name for x in library_facts([t])]
    assert "PyLeanX.Harmonic.coeff" in names
    src = t.to_lean()
    assert "noncomputable def PyLeanX.Harmonic.coeff" in src
    assert src.index("def PyLeanX.Harmonic.coeff") < src.index("theorem t")


def test_catalogue():
    shipped = [v for v in ha.LEMMAS.values() if isinstance(v, LibraryFact)]
    assert len(shipped) >= 18
    for fact in shipped:
        assert "sorry" not in fact.lean and fact.name in fact.lean
        assert LIBRARY_FACTS[fact.name] is fact
    for name in ("parseval", "bessel_summable", "riemann_lebesgue_coeff", "riemann_lebesgue",
                 "gaussian", "inversion", "coeff_derivative", "coeff_eq_integral"):
        assert name in ha.LEMMAS


@pytest.fixture(scope="module")
def lecture():
    sys.path.insert(0, str(EXAMPLES))
    try:
        import harmonic_lecture

        yield harmonic_lecture
    finally:
        sys.path.remove(str(EXAMPLES))


def test_lecture_solutions_and_figures(lecture):
    sols = lecture.all_solutions()
    assert len(sols) == 6
    for thm in sols:
        assert "sorry" not in thm.to_lean() and "∎" in str(thm.prose())
    assert "f(x) = (f̂)^(∨)(x)" in str(lecture.solution("uniqueness").prose())
    svg, note = lecture.figure_partial_sums(31)
    assert svg.startswith("<svg") and "Gibbs" in note
    assert lecture.figure_decay().startswith("<svg")
    for build in lecture.EXERCISES.values():
        assert build().proof is None
    nb = json.loads((EXAMPLES / "lecture_harmonic_analysis.ipynb").read_text(encoding="utf-8"))
    code = "\n".join("".join(c["source"]) for c in nb["cells"] if c["cell_type"] == "code")
    for name in ("decay", "riemann_lebesgue_l2", "uniqueness", "exercise_3", "explore_gaussian"):
        assert name in code and hasattr(lecture, name)

"""The analysis pack, without Lean: registration, activation, numerics, chapter."""

from __future__ import annotations

import math
import random

import pyleanx_analysis as an
from pyleanx_analysis import numeric
from pyleanx_analysis.chapters import integration as ch

import pyleanx as pl
from pyleanx import realvar as rv
from pyleanx.render.lean import theorem_packs

f = pl.symbol("f", pl.Fn(pl.Real, pl.Real))
x, t, a, b = pl.symbols("x t a b", pl.Real)


def _thm(name: str, hyps: dict, concl: object) -> pl.Theorem:
    return pl.Theorem(name, [f, x, a, b], assumptions=hyps, conclusion=concl,
                      proof=pl.proof(pl.conclude()))


def test_the_pack_is_registered_and_discoverable():
    from pyleanx import justify
    from pyleanx.packs import load_plugins

    assert an.pack.name == "analysis" and "analysis" in justify.packs()
    assert load_plugins().get("analysis") == "pyleanx_analysis"


def test_rules_apply_only_to_measure_theoretic_theorems():
    assert "analysis" in theorem_packs(ch.markov)
    plain = _thm("plain", {"hx": x > 0}, x >= 0)
    assert "analysis" not in theorem_packs(plain)
    assert "MeasureTheory.Integrable.abs ‹_›" in ch.markov.to_lean()
    assert "MeasureTheory.Integrable.abs ‹_›" not in plain.to_lean()


def test_the_textbook_proof_is_shorter_than_the_core_one():
    assert len(ch.markov.proof.flat()) == 1 and len(ch.markov_core.proof.flat()) == 3
    assert len(ch.interval_bound.proof.flat()) == 1


def test_derivatives_and_integrals_are_accurate():
    assert abs(numeric.derivative(math.sin, 0.7) - math.cos(0.7)) < 1e-9
    assert abs(numeric.derivative(lambda s: s ** 3, 2.0) - 12.0) < 1e-8
    assert abs(numeric.integral(math.exp, 0.0, 1.0) - (math.e - 1)) < 1e-10
    assert abs(numeric.integral(lambda s: s * s, 2.0, -1.0) + 3.0) < 1e-10    # oriented


def test_sampled_functions_know_their_properties():
    rng = random.Random(1)
    samples = [numeric.sample_function(rng) for _ in range(40)]
    assert any(s.integrable for s in samples) and any(not s.integrable for s in samples)
    for s in samples:
        if s.integrable:      # decays: the integral over ℝ is the integral over [-40, 40]
            assert abs(s(40.0)) < 1e-12


def test_a_defining_hypothesis_builds_the_function():
    sq = {"hf": pl.Forall(t, f(t) == t ** 2 + 1)}
    assert _thm("d_ok", sq, an.deriv(f, x) == 2 * x).sanity_check().ok
    assert "looks false" in str(_thm("d_bad", sq, an.deriv(f, x) == x ** 2).sanity_check())
    cube = {"hf": pl.Forall(t, f(t) == 3 * t ** 2)}
    integral = pl.integral(lambda s: f(s), pl.Real, bounds=(a, b))
    assert _thm("ftc_ok", cube, integral == b ** 3 - a ** 3).sanity_check().ok
    assert "looks false" in str(_thm("ftc_bad", cube, integral == b ** 3 + a ** 3).sanity_check())


def test_hypotheses_about_sampled_functions_are_evaluated_honestly():
    def thm(name: str, concl: object) -> pl.Theorem:
        return pl.Theorem(name, [f], assumptions={"hi": rv.integrable(f)}, conclusion=concl,
                          proof=pl.proof(pl.conclude()))

    assert "looks false" in str(thm("l1", rv.l1_norm(f) > 1000).sanity_check())
    assert thm("l1_ok", rv.l1_norm(f) >= 0).sanity_check().ok   # only integrable samples


def test_hints_explain_analysis_failures():
    from pyleanx.diagnose import _hint

    assert "integrability" in _hint("failed to synthesize MeasureTheory.Integrable")
    assert "finite" in _hint("unsolved goals ⊢ volume K ≠ ⊤")

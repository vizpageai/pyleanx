"""Real Lean: explanations are the proofs Lean verified (compiled vs re-elaborated)."""

from __future__ import annotations

import pytest

import pyleanx as pl

pytestmark = pytest.mark.lean


def test_rewrite_proof_is_exact_with_every_rule(lean_project):
    e = pl.explain("Complex.sin_sq_add_cos_sq", project=lean_project, refresh=True,
                   timeout=3600)
    assert e.exact, e.evidence
    assert e.evidence["value_hash"] == e.evidence["replayed_value_hash"]
    assert e.evidence["modified"] is False
    rules = [s.text.rstrip(",") for s in e.steps if s.depth == 1]
    assert rules[:4] == ["cosh_mul_I", "sinh_mul_I", "mul_pow", "I_sq"]
    first = next(s for s in e.steps if s.text.startswith("cosh_mul_I"))
    assert "cosh (x * I) ^ 2" in first.goals_before[0]
    assert "cos x ^ 2 - sinh (x * I) ^ 2" in first.goals_after[0]
    assert "Complex.cosh_sq_sub_sinh_sq" in e.cited
    assert "Complex.I ^ 2 = -1" in e.lemmas["Complex.I_sq"].statement


def test_simp_step_lists_the_lemmas_it_used(lean_project):
    e = pl.explain("Real.sin_sq_add_cos_sq", project=lean_project, refresh=True, timeout=3600)
    assert e.exact, e.evidence
    (step,) = [s for s in e.steps if s.text.startswith("simp")]
    assert {"Complex.ofReal_sin", "Complex.ofReal_cos",
            "Complex.sin_sq_add_cos_sq"} <= set(step.uses)
    assert step.closes

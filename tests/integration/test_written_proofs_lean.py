"""Real Lean: written proofs across domains, avoid=, shipped library facts, and rejection of
a circular proof and of a false step."""

from __future__ import annotations

import runpy
from pathlib import Path

import pytest

import pyleanx as pl
from pyleanx import analysis as an
from pyleanx import numbers as nt

pytestmark = pytest.mark.lean

EXAMPLES = Path(__file__).resolve().parents[2] / "examples"
READABLE = ["trig", "side_splitter", "am_gm", "infinite_primes", "consecutive_even",
            "limit_sum", "group_abelian", "bernoulli", "cauchy_integral"]


def _thm(name: str) -> pl.Theorem:
    ns = runpy.run_path(str(EXAMPLES / f"readable_{name}.py"))
    return next(v for v in ns.values() if isinstance(v, pl.Theorem))


def test_written_proofs_verify_and_bad_ones_are_rejected(lean_project):
    good = [_thm(n) for n in READABLE]
    x = pl.symbol("x", pl.Real)
    circular = pl.Theorem("circular_trig", [x], conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
                          avoid=[an.sin_sq_add_cos_sq], proof=pl.simp())
    n, p = pl.symbols("n p", pl.Nat)
    false_step = pl.Theorem(
        "false_step", [n], assumptions={"h": nt.even(n)}, conclusion=nt.even(n * n),
        proof=pl.proof(pl.claim(nt.odd(n), because="h"), pl.conclude()))
    from pyleanx import complex_analysis as ca

    cif = good[-1]
    cif_cheat = pl.Theorem(
        "cif_cheat", cif.variables, [(h.name, h.prop) for h in cif.assumptions], cif.conclusion,
        avoid=ca.INTEGRAL_FORMULA,
        proof=pl.exact(pl.ref("DifferentiableOn.circleIntegral_sub_inv_smul")("hf", "hw")))
    results = pl.verify_all([*good, circular, false_step, cif_cheat], project=lean_project,
                            use_cache=False, timeout=3600)
    for t, r in zip(good, results, strict=False):
        assert r.verified, (t.name, [d.message for d in r.diagnostics])
        assert set(r.axioms) <= {"propext", "Classical.choice", "Quot.sound"}
        assert "Checked by Lean" in str(t.prose(r))
    bad = results[len(good)]
    assert bad.status is pl.Status.REJECTED
    assert any("Real.sin_sq_add_cos_sq" in d.message and d.span_kind == "avoid_check"
               for d in bad.diagnostics)
    wrong = results[len(good) + 1]
    assert wrong.status is pl.Status.REJECTED and not wrong.verified
    assert "did not accept" in str(false_step.prose(wrong))
    cheat = results[-1]
    assert cheat.status is pl.Status.REJECTED
    assert any("DifferentiableOn.circleIntegral_sub_inv_smul" in d.message
               for d in cheat.diagnostics)

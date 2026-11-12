"""Real Lean: written proofs (claims with reasons), avoid=, and shipped library facts."""

from __future__ import annotations

import runpy
from pathlib import Path

import pytest

import pyleanx as pl
from pyleanx import analysis as an

pytestmark = pytest.mark.lean

EXAMPLES = Path(__file__).resolve().parents[2] / "examples"


def _thm(file: str, var: str) -> pl.Theorem:
    return runpy.run_path(str(EXAMPLES / file))[var]


def test_written_proofs_verify_and_circular_proof_is_rejected(lean_project):
    good = [_thm("readable_trig.py", "pythagorean_identity"),
            _thm("readable_side_splitter.py", "side_splitter"),
            _thm("readable_am_gm.py", "am_gm")]
    x = pl.symbol("x", pl.Real)
    circular = pl.Theorem("circular_trig", [x], conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
                          avoid=[an.sin_sq_add_cos_sq], proof=pl.simp())
    results = pl.verify_all([*good, circular], project=lean_project, use_cache=False,
                            timeout=2400)
    for t, r in zip(good, results, strict=True):
        assert r.verified, (t.name, [d.message for d in r.diagnostics])
        assert set(r.axioms) <= {"propext", "Classical.choice", "Quot.sound"}
        assert "Checked by Lean" in str(t.prose(r))
    bad = results[-1]
    assert bad.status is pl.Status.REJECTED
    assert any("Real.sin_sq_add_cos_sq" in d.message and d.span_kind == "avoid_check"
               for d in bad.diagnostics)

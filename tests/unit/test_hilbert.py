"""The Hilbert transform vocabulary and the written proofs of examples/hilbert_transform.py (no Lean)."""

from __future__ import annotations

import sys
from pathlib import Path

import pyleanx as pl
from pyleanx import hilbert as hil

EXAMPLES = Path(__file__).resolve().parents[2] / "examples"


def test_statements_use_shipped_definitions():
    f = pl.symbol("f", hil.L2)
    t = pl.Theorem("t", [f], conclusion=pl.norm(hil.H(f)) == pl.norm(f))
    src = t.to_lean()
    assert "noncomputable def PyLeanX.Hilbert.hilbert" in src
    assert "noncomputable def PyLeanX.Hilbert.mulSymbol" in src
    assert "MeasureTheory.Lp ℂ 2" in src and "sorry" not in src
    assert "Hf" in str(t.prose()).replace(" ", "")


def test_hilbert_transform_proofs_render():
    sys.path.insert(0, str(EXAMPLES))
    try:
        import hilbert_transform as ht
    finally:
        sys.path.remove(str(EXAMPLES))
    assert len(ht.THEOREMS) == 6
    for thm in ht.THEOREMS:
        assert "sorry" not in thm.to_lean() and "not yet checked by Lean" in str(thm.prose())
    assert "MeasureTheory.Lp.norm_fourier_eq" in ht.isometry.to_lean()

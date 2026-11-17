"""The Calderón–Zygmund vocabulary and the written proofs of examples/calderon_zygmund.py (no Lean)."""

from __future__ import annotations

import sys
from pathlib import Path

import pyleanx as pl
from pyleanx import realvar as rv

EXAMPLES = Path(__file__).resolve().parents[2] / "examples"


def test_lebesgue_differentiation_is_shipped_with_its_proof():
    f = pl.symbol("f", rv.RFun)
    t = pl.Theorem("t", [f], assumptions={"hf": rv.locally_integrable(f)},
                   conclusion=rv.almost_every(lambda p: pl.abs(f(p)) >= 0),
                   proof=pl.proof(pl.claim(rv.almost_every(lambda p: pl.abs(f(p)) >= 0),
                                           because=[rv.lebesgue_differentiation, "hf"]),
                                  pl.conclude()))
    src = t.to_lean()
    assert "theorem PyLeanX.Real.lebesgue_differentiation" in src
    assert "IsUnifLocDoublingMeasure.ae_tendsto_average" in src


def test_limits_as_r_tends_to_zero_plus_read_as_in_a_book():
    f = pl.symbol("f", rv.RFun)
    x = pl.symbol("x", pl.Real)
    stmt = rv.tendsto_zero_plus(lambda t: pl.abs(f(t)), pl.abs(f(x)))
    t = pl.Theorem("t", [f, x], conclusion=stmt)
    assert "nhdsWithin 0 (Set.Ioi 0)" in t.to_lean()
    assert "0⁺" in str(t.prose())


def test_calderon_zygmund_proofs_render():
    sys.path.insert(0, str(EXAMPLES))
    try:
        import calderon_zygmund as cz
    finally:
        sys.path.remove(str(EXAMPLES))
    assert [t.name for t in cz.THEOREMS] == ["cz_interval_average", "cz_good_part",
                                             "calderon_zygmund"]
    for thm in cz.THEOREMS:
        assert "sorry" not in thm.to_lean() and "not yet checked by Lean" in str(thm.prose())
    # the decomposition cites theorems 7, 8, 15 and 16, which are emitted with their proofs
    src = cz.decomposition.to_lean()
    for name in ("maximal_level_set_open", "maximal_level_set_bound", "cz_interval_average",
                 "cz_good_part"):
        assert f"theorem {name}" in src

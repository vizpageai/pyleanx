"""Real-variable vocabulary and the written proofs of examples/singular_integrals.py (no Lean)."""

from __future__ import annotations

import sys
from pathlib import Path

import pyleanx as pl
from pyleanx import realvar as rv
from pyleanx.serialize import theorem_from_canonical

EXAMPLES = Path(__file__).resolve().parents[2] / "examples"


def test_subset_is_lean_infix_and_set_notation_renders():
    s, v = pl.symbols("s v", rv.Indices)
    c, r = pl.symbols("c r", rv.Family)
    f = pl.symbol("f", rv.RFun)
    t = pl.Theorem("t", [s, v, c, r, f], assumptions={"h": rv.subset(v, s)},
                   conclusion=rv.measure(rv.union(v, c, r)) <= pl.sum(
                       v, lambda j: rv.measure(rv.interval(c(j), r(j))), sort=pl.Nat))
    src = t.to_lean()
    assert "(h : v ⊆ s)" in src and "⋃ i ∈ v, Metric.closedBall (c i) (r i)" in src
    assert "MeasureTheory.Measure.real MeasureTheory.volume" in src
    text = str(t.prose())
    assert "v ⊆ s" in text and "|⋃_(i ∈ v) [c(i) - r(i), c(i) + r(i)]|" in text
    g = pl.integral(lambda x: pl.abs(f(x)), within=rv.interval(0, 1))
    t2 = pl.Theorem("t2", [f], conclusion=g >= 0)
    assert "∫ x in (Metric.closedBall 0 1), abs (f x)" in t2.to_lean()
    again = theorem_from_canonical(t.canonical())
    assert "(h : v ⊆ s)" in again.to_lean()


def test_singular_integrals_proofs_render():
    sys.path.insert(0, str(EXAMPLES))
    try:
        import singular_integrals as si
    finally:
        sys.path.remove(str(EXAMPLES))
    assert len(si.THEOREMS) >= 3
    for thm in si.THEOREMS:
        assert "sorry" not in thm.to_lean() and "∎" in str(thm.prose())
    text = str(si.covering_bound.prose())
    assert "Vitali covering lemma (theorem 1)" in text


def test_singular_lecture_figures():
    sys.path.insert(0, str(EXAMPLES))
    try:
        import singular_lecture as sl
    finally:
        sys.path.remove(str(EXAMPLES))
    fam = sl._intervals(20, 7)
    chosen = sl.vitali_select(fam)
    for a in chosen:  # pairwise disjoint
        for b in chosen:
            if a != b:
                assert abs(fam[a][0] - fam[b][0]) > fam[a][1] + fam[b][1]
    svg, note = sl.figure_vitali(20, 7)
    assert svg.startswith("<svg") and "<b>True</b>" in note
    svg, note = sl.figure_maximal(0.5)
    assert svg.startswith("<svg") and "theorem 5" in note

"""Real Lean: proof graphs report Lean's own dependencies and axioms."""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import analysis as an

pytestmark = pytest.mark.lean


def test_core_lemma_has_no_axioms(lean_project):
    g = pl.proof_graph("Nat.add_comm", depth=2, project=lean_project, refresh=True,
                       timeout=1800)
    assert g.axioms == ()
    assert {"Nat.zero_add", "Nat.succ_add"} <= set(g.uses("Nat.add_comm"))
    assert "Nat" in g.primitives and g.closure["declarations"] > 10
    assert "rfl" not in g.nodes  # base logic is summarised, not drawn
    assert "rfl" in pl.proof_graph("Nat.add_comm", depth=3, detail="all", project=lean_project,
                                   timeout=1800).nodes


def test_axioms_match_the_verification_audit(lean_project):
    g = pl.proof_graph(an.sin_sq_add_cos_sq, depth=2, project=lean_project, refresh=True,
                       timeout=1800)
    assert g.axioms == ("Classical.choice", "Quot.sound", "propext")
    assert {"Real.sin", "Real.cos"} <= set(g.nodes)
    x = pl.symbol("x", pl.Real)
    r = pl.Theorem("pg_trig", [x], conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
                   proof=pl.exact(an.sin_sq_add_cos_sq(x))).verify(project=lean_project,
                                                                    timeout=1800)
    assert r.verified and tuple(sorted(r.axioms or ())) == g.axioms
    print(g)

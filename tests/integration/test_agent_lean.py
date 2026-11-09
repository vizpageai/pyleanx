"""M8 gate (real Lean REPL + batch): agents find proofs, but only the batch audit verifies.

A "lying" agent that closes goals with `sorry` (or trusts `native_decide`) sees the REPL
report the goal closed, and is still rejected by the final audit.
"""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import agent

pytest.importorskip("lean_interact")
pytestmark = [pytest.mark.lean, pytest.mark.interactive]

T = 1800


def _problems(*names):
    by = {p.name: p for p in agent.basic()}
    return [by[n] for n in names]


def test_m8_baseline_search_verifies_with_batch_audit(lean_project):
    for p in _problems("b_imp_self", "b_binomial", "b_le_trans"):
        att = agent.search_proof(p.build(), project=lean_project, max_depth=3,
                                 verify_timeout=T)
        assert att.verified, (p.name, att.to_dict())
        assert att.result.status is pl.Status.VERIFIED
        assert "sorryAx" not in (att.result.axioms or ())
    pl.shutdown_sessions()


def test_m8_lying_agent_is_rejected_by_audit(lean_project):
    P = pl.prop_symbol("P")
    thm = pl.Theorem("m8_lie", [P], conclusion=P)  # unprovable
    env = agent.ProofEnv(thm, lean_project, allow_raw=True)
    out = env.act("sorry")
    assert out["ok"], out  # Lean elaborates `sorry` (with a warning)
    res = env.verify(use_cache=False, timeout=T)
    # Either the REPL already reports the proof as not complete (nothing to verify),
    # or the batch audit rejects it; it is never verified.
    if res is not None:
        assert res.status is pl.Status.POLICY_REJECTED, res.summary()
        assert "sorryAx" in (res.axioms or ())
    assert not env.observe()["verified"]

    # native_decide closes the goal in the REPL; only the axiom audit catches it.
    n = pl.nat(2)
    thm2 = pl.Theorem("m8_native", [], conclusion=n + 2 == 4)
    env2 = agent.ProofEnv(thm2, lean_project, allow_raw=True)
    out = env2.act("native_decide")
    assert out["ok"] and out["complete"], out
    res2 = env2.verify(use_cache=False, timeout=T)
    assert res2 is not None and res2.status is pl.Status.POLICY_REJECTED, res2.summary()
    assert any("_native" in a for a in res2.axioms or ())
    pl.shutdown_sessions()


def test_m8_tool_calls_and_batch_mode(lean_project):
    thm = _problems("b_am_gm")[0].build()
    env = agent.ProofEnv(thm, lean_project, allow_raw=True)
    assert env.call_tool("get_state")["goals"]
    r = env.call_tool("apply_tactic", {"tactic": "linarith"})
    assert not r["ok"] and r["error"]
    r = env.call_tool("apply_tactic", {"tactic": "nlinarith [sq_nonneg (a - b)]"})
    assert r["ok"] and r["complete"], r
    v = env.call_tool("verify")
    assert v["verified"] is True and v["status"] == "verified", v
    pl.shutdown_sessions()

    # REPL-free baseline: whole candidate proofs in one batch run, winner re-verified
    nat = _problems("b_nat_add_zero")[0].build()
    att = agent.try_proofs(nat, [pl.positivity(), pl.simp()], lean_project, timeout=T)
    assert att.verified and att.script == ["simp"], att.to_dict()

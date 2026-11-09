"""M8 agent API: parsing, environment bookkeeping, search control (fake REPL).

Nothing here asserts `verified`; that is only tested with real Lean
(tests/integration/test_agent.py).
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest
from test_session import FakeRepl  # tests/unit is on sys.path (rootdir import mode)

import pyleanx as pl
from pyleanx import agent
from pyleanx import session as session_mod
from pyleanx.proofs import RawTactic

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean-project"


@pytest.fixture
def fake(monkeypatch):
    repl = FakeRepl()
    monkeypatch.setattr(session_mod, "get_repl", lambda project, launch: repl)
    return repl


def _imp():
    P = pl.prop_symbol("P")
    return pl.Theorem("imp", [P], conclusion=pl.Implies(P, P))


@pytest.mark.parametrize("text,lean", [
    ("ring", "ring"),
    ("linarith", "linarith"),
    ("linarith [h1, h2]", "linarith [h1, h2]"),
    ("nlinarith [sq_nonneg]", "nlinarith [sq_nonneg]"),
    ("norm_num", "norm_num"),
    ("simp", "simp"),
    ("simp only [add_zero] at h", "simp only [add_zero] at h"),
    ("intro x y", "intro x y"),
    ("exact h", "exact h"),
    ("exact dist_triangle A B C", "exact dist_triangle A B C"),
    ("apply le_trans", "apply le_trans"),
    ("rw [← mul_comm, h] at h2", "rw [← mul_comm, h] at h2"),
    ("rw [<- h]", "rw [← h]"),
])
def test_structured_parsing(text, lean):
    t = agent.tactic_from_text(text)
    assert not isinstance(t, RawTactic)
    assert str(t) == lean


def test_parsed_lemmas_carry_catalog_imports():
    t = agent.tactic_from_text("exact Real.exp_pos x")
    assert "Mathlib.Analysis.SpecialFunctions.Exp" in t.imports()


@pytest.mark.parametrize("text", [
    "nlinarith [sq_nonneg (a - b)]",
    "exact ⟨h.2, h.1⟩",
    "intro h; exact h",
    "constructor <;> simp",
    "use z + 1",
    "sorry",
])
def test_unstructured_text_is_raw_only_when_allowed(text):
    with pytest.raises(pl.TacticError, match="raw"):
        agent.tactic_from_text(text)
    t = agent.tactic_from_text(text, allow_raw=True)
    assert isinstance(t, RawTactic)


def test_raw_text_records_needed_imports():
    t = agent.tactic_from_text("nlinarith [sq_nonneg (a - b)]", allow_raw=True)
    assert "Mathlib.Tactic.Linarith" in t.imports()
    assert "Mathlib.Algebra.Order.Ring.Unbundled.Basic" in t.imports()


def test_env_observe_act_undo_transcript(fake):
    env = agent.ProofEnv(_imp(), PROJECT)
    obs = env.observe()
    assert obs["theorem"] == "imp" and obs["goals"] == ["⊢ goal"] and not obs["complete"]
    assert "theorem imp (P : Prop) :" in obs["statement"]
    bad = env.act("nonsense_tactic")
    assert not bad["ok"]
    out = env.act("intro h")
    assert out["ok"] and out["goals"] == ["h : P\n⊢ P"]
    assert env.undo()["ok"]
    env.act("intro h")
    out = env.act("exact h")
    assert out["complete"] and env.observe()["complete"]
    assert not env.observe()["verified"]  # REPL completion is not verification
    lines = env.transcript_jsonl().strip().splitlines()
    assert [json.loads(x)["event"] for x in lines][:2] == ["open", "act"]


def test_env_raw_requires_opt_in(fake):
    env = agent.ProofEnv(_imp(), PROJECT)
    r = env.act("intro h; exact h")
    assert not r["ok"] and "raw" in r["error"]
    env2 = agent.ProofEnv(_imp(), PROJECT, allow_raw=True)
    assert env2.project.policy.allow_raw_tactics
    assert not agent.ProofEnv(_imp(), PROJECT).project.policy.allow_raw_tactics


def test_env_accepts_canonical_tactic_json(fake):
    env = agent.ProofEnv(_imp(), PROJECT)
    assert env.act(["intro", ["h"]])["ok"]
    assert env.act(["exact", ["name", "h"]])["complete"]


def test_step_budget(fake):
    env = agent.ProofEnv(_imp(), PROJECT, max_steps=1)
    env.act("nonsense")
    assert "budget" in env.act("ring")["error"]


def test_tools_schema_and_dispatch(fake):
    names = {t["name"] for t in agent.TOOLS}
    assert names == {"get_state", "apply_tactic", "undo", "verify"}
    for t in agent.TOOLS:
        assert t["input_schema"]["type"] == "object"
    env = agent.ProofEnv(_imp(), PROJECT)
    assert env.call_tool("get_state")["goals"] == ["⊢ goal"]
    assert env.call_tool("apply_tactic", {"tactic": "intro h"})["ok"]
    assert env.call_tool("verify") == {"verified": False, "error": "goals remain"}
    assert not env.call_tool("bogus")["ok"]


def test_automation_proposer_shapes():
    p = agent.AutomationProposer()
    assert p({"goals": ["⊢ ∀ (x y : ℝ), x = x"]})[0] == "intro x y"
    assert p({"goals": ["h1 : P\n⊢ P → Q"]})[0] == "intro h2"
    assert "constructor" in p({"goals": ["⊢ P ∧ Q"]})
    assert p({"goals": []}) == []


def test_retrieval_proposer_uses_bank():
    bank = pl.TheoremBank()
    form = pl.Formalization("lean4", "mathlib", "t", "r")
    bank.add_declaration("geometry.tri", "dist_triangle", "dist x z ≤ dist x y + dist y z", form,
                         aliases=("triangle inequality",))
    cands = agent.RetrievalProposer(bank)({"goals": ["⊢ dist A C ≤ dist A B + dist B C"]})
    assert "apply dist_triangle" in cands


def test_search_finds_script_and_status_comes_from_batch_result(fake, monkeypatch):
    calls = []

    def fake_verify(self, *, use_cache=True, timeout=None):
        calls.append(self.session.history)
        self.result = pl.VerificationResult(theorem="imp", status=pl.Status.POLICY_REJECTED)
        return self.result

    monkeypatch.setattr(agent.ProofEnv, "verify", fake_verify)
    att = agent.search_proof(_imp(), project=PROJECT)
    assert att.script == ["ring"]  # FakeRepl: `ring` closes any goal
    assert calls, "a complete script must go to the batch verifier"
    assert att.status == "rejected" and not att.verified


def test_search_backtracks_and_respects_budget(fake):
    def proposer(obs):
        return ["intro h", "nonsense"] if obs["goals"] == ["⊢ goal"] else ["nonsense"]

    att = agent.search_proof(_imp(), proposer, PROJECT, max_depth=3, max_expansions=10)
    assert att.status == "incomplete" and att.script == []  # undone after dead end
    assert att.expansions <= 10


def test_benchmark_problems_build_and_export(tmp_path):
    probs = agent.basic()
    assert len(probs) >= 12
    names = [p.build().name for p in probs]
    assert len(set(names)) == len(names)
    path = agent.export_jsonl(tmp_path / "basic.jsonl")
    rows = [json.loads(x) for x in path.read_text(encoding="utf-8").splitlines()]
    assert rows[0]["theorem"]["proof"] is None and "theorem" in rows[0]["lean"]
    again = pl.theorem_from_canonical(rows[5]["theorem"])
    assert again.name == rows[5]["name"]

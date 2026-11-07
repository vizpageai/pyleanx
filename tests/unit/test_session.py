"""Session bookkeeping against a scripted fake REPL.

These tests cover history/undo/replay/policy logic only. They never assert that
anything is *verified*: that is exclusively tested with real Lean in
tests/integration/test_interactive.py.
"""

import dataclasses

import pytest

import pyleanx as pl
from pyleanx import session as session_mod
from pyleanx.backend.leaninteract import ReplError, StepOutcome


class FakeRepl:
    """Goals are a counter: tactic 'ring'/'exact h' closes, 'intro h' opens one step."""

    def __init__(self):
        self.imports_seen = []
        self.next_state = 0
        self.states = {}
        self.fail_next_step = False
        self.opened = 0

    def import_env(self, imports, timeout):
        self.imports_seen.append(tuple(imports))
        return len(self.imports_seen) - 1

    def _new(self, goals, status):
        sid = self.next_state
        self.next_state += 1
        self.states[sid] = goals
        return sid

    def open_statement(self, code, env, timeout):
        self.opened += 1
        assert code.rstrip().endswith("sorry") and "theorem" in code
        sid = self._new(("⊢ goal",), "Incomplete")
        return StepOutcome(True, sid, ("⊢ goal",), "Incomplete: open goals remain", ())

    def step(self, proof_state, tactic, timeout):
        if self.fail_next_step:
            self.fail_next_step = False
            raise ReplError("simulated crash")
        if tactic in ("ring", "exact h", "positivity"):
            sid = self._new((), "Completed")
            return StepOutcome(True, sid, (), "Completed", ())
        if tactic == "intro h":
            sid = self._new(("h : P\n⊢ P",), "Incomplete")
            return StepOutcome(True, sid, ("h : P\n⊢ P",), "Incomplete: open goals remain", ())
        return StepOutcome(False, None, (), "Error", (), f"unknown tactic {tactic}")


@pytest.fixture
def fake(monkeypatch):
    repl = FakeRepl()
    monkeypatch.setattr(session_mod, "get_repl", lambda project, launch: repl)
    return repl


def _imp():
    P = pl.prop_symbol("P")
    return pl.Theorem("imp", [P], conclusion=pl.Implies(P, P))


def test_apply_goals_history_and_finish(fake):
    s = _imp().session(".")
    assert s.goals == ("⊢ goal",) and not s.is_complete
    r = s.apply(pl.intro("h"))
    assert r.ok and r and r.goals == ("h : P\n⊢ P",) and not r.complete
    r = s.apply(pl.exact("h"))
    assert r.complete and s.is_complete
    assert [type(t).__name__ for t in s.history] == ["Intro", "Exact"]
    thm = s.finish()
    assert "  intro h\n  exact h" in thm.to_lean()


def test_failed_step_leaves_state_unchanged(fake):
    s = _imp().session(".")
    r = s.apply(pl.omega())
    assert not r.ok and not r and "unknown tactic" in r.error
    assert s.history == () and s.goals == ("⊢ goal",)
    # apply(...) with several tactics stops at the first failure
    r = s.apply(pl.intro("h"), pl.omega(), pl.exact("h"))
    assert not r.ok and len(s.history) == 1


def test_peek_does_not_commit(fake):
    s = _imp().session(".")
    r = s.peek(pl.ring())
    assert r.complete and s.history == () and not s.is_complete


def test_undo_and_reset(fake):
    s = _imp().session(".")
    s.apply(pl.intro("h"), pl.exact("h"))
    assert s.undo() == ("h : P\n⊢ P",) and len(s.history) == 1
    assert s.reset() == ("⊢ goal",) and s.history == ()
    with pytest.raises(pl.TacticError):
        s.undo()


def test_finish_requires_complete_proof(fake):
    s = _imp().session(".")
    with pytest.raises(pl.TacticError, match="no tactics"):
        s.finish()
    s.apply(pl.intro("h"))
    with pytest.raises(pl.TacticError, match="incomplete"):
        s.finish()
    assert s.theorem.proof is None  # nothing attached on failure


def test_crash_restarts_and_replays(fake):
    s = _imp().session(".")
    s.apply(pl.intro("h"))
    fake.fail_next_step = True
    r = s.apply(pl.exact("h"))
    assert r.complete and fake.opened == 2  # reopened statement, replayed intro, retried


def test_new_import_reopens_with_union(fake):
    n = pl.symbol("n", pl.Nat)
    s = pl.Theorem("t", [n], conclusion=n + 0 == n).session(".")
    assert fake.imports_seen[-1] == ()  # core-only statement: nothing preloaded
    s.apply(pl.ring())  # needs Mathlib.Tactic.Ring
    assert "Mathlib.Tactic.Ring" in fake.imports_seen[-1] and fake.opened == 2


def test_mathlib_statement_preloads_common_tactics(fake):
    x = pl.symbol("x", pl.Real)
    pl.Theorem("t", [x], conclusion=x**2 >= 0).session(".")
    assert "Mathlib.Tactic.Linarith" in fake.imports_seen[-1]


def test_raw_tactics_gated_in_sessions(fake):
    s = _imp().session(".")
    with pytest.raises(pl.TacticError, match="allow_raw_tactics"):
        s.apply(pl.raw_tactic("intro h"))
    proj = pl.LeanProject.at(".")
    proj = proj.with_(policy=dataclasses.replace(proj.policy, allow_raw_tactics=True))
    s2 = _imp().session(proj)
    assert s2.apply(pl.raw_tactic("intro h")).ok
    with pytest.raises(pl.TacticError, match="forbidden"):
        s2.apply(pl.raw_tactic("intro h\naxiom bad : False"))


def test_displays(fake):
    s = _imp().session(".")
    assert "1 goal" in s.goals._repr_markdown_()
    r = s.apply(pl.omega())
    assert "❌" in r._repr_markdown_()
    s.apply(pl.intro("h"), pl.exact("h"))
    assert "No goals" in s.goals._repr_markdown_() and "intro h" in s._repr_markdown_()
    assert "2 step(s)" in repr(s)

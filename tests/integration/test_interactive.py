"""M5 gate with the real Lean REPL (LeanInteract).

Gate: a user can apply `intro` then `exact` across successive interactive steps and
verify the final theorem with the batch backend; incomplete proofs show open goals
and remain unverified.
"""

import dataclasses
import time

import pytest

import pyleanx as pl

pytest.importorskip("lean_interact")
pytestmark = [pytest.mark.lean, pytest.mark.interactive]


@pytest.fixture(scope="module", autouse=True)
def _stop_repls():
    yield
    pl.shutdown_sessions()


def test_gate_intro_then_exact_then_batch_verify(lean_project):
    P = pl.prop_symbol("P")
    thm = pl.Theorem("session_imp", [P], conclusion=pl.Implies(P, P))
    s = thm.session(lean_project)
    assert len(s.goals) == 1 and "⊢ P → P" in s.goals[0]
    r1 = s.apply(pl.intro("h"))
    assert r1.ok and len(r1.goals) == 1 and "h : P" in r1.goals[0] and not s.is_complete
    r2 = s.apply(pl.exact("h"))
    assert r2.complete and s.is_complete
    result = s.verify()
    assert result.verified, result.summary()
    assert result.backend == "subprocess"  # the authoritative batch backend decided


def test_incomplete_proof_shows_goals_and_is_never_verified(lean_project):
    P, Q = pl.prop_symbol("P"), pl.prop_symbol("Q")
    thm = pl.Theorem("session_incomplete", [P, Q],
                     conclusion=pl.Implies(P, Q, pl.And(P, Q)))
    s = thm.session(lean_project)
    s.apply(pl.intro("hp", "hq"), pl.constructor())
    assert len(s.goals) == 2 and not s.is_complete
    with pytest.raises(pl.TacticError, match="incomplete"):
        s.verify()
    assert thm.proof is None
    s.apply(pl.exact("hp"))
    assert len(s.goals) == 1 and not s.is_complete


def test_mathlib_session_fast_steps_errors_undo(lean_project):
    x, y = pl.symbols("x y", pl.Real)
    thm = pl.Theorem("session_square", [x, y],
                     conclusion=(x + y) ** 2 == x**2 + 2 * x * y + y**2)
    s = thm.session(lean_project)  # first Mathlib session pays the import cost
    t0 = time.perf_counter()
    bad = s.apply(pl.positivity())
    assert not bad.ok and bad.error and s.history == ()
    good = s.peek(pl.ring())
    assert good.complete and s.history == ()
    s.apply(pl.ring())
    steps_s = time.perf_counter() - t0
    print(f"\n[perf] 3 interactive steps after warm-up: {steps_s:.2f}s")
    assert s.is_complete and steps_s < 30
    s.undo()
    assert not s.is_complete
    s.apply(pl.ring())

    # A second session on the same imports reuses the loaded environment.
    t0 = time.perf_counter()
    s2 = pl.Theorem("session_square2", [x], conclusion=x**2 + 1 > 0).session(lean_project)
    s2.apply(pl.positivity())
    reuse_s = time.perf_counter() - t0
    print(f"[perf] second session open + step: {reuse_s:.2f}s")
    assert s2.is_complete and reuse_s < 30

    results = pl.verify_all([s.finish(), s2.finish()], project=lean_project)
    assert all(r.verified for r in results), [r.summary() for r in results]


def test_sorry_in_session_never_verifies(lean_project):
    proj = lean_project.with_(policy=dataclasses.replace(lean_project.policy,
                                                         allow_raw_tactics=True))
    x = pl.symbol("x", pl.Real)
    thm = pl.Theorem("session_sorry", [x], conclusion=x**2 < 0)
    s = thm.session(proj)
    r = s.apply(pl.raw_tactic("sorry"))
    if s.is_complete:  # the REPL may consider the goal closed...
        result = s.verify()
        assert result.status is pl.Status.POLICY_REJECTED and not result.verified
    else:  # ...or report it as incomplete; either way nothing is verified
        assert r.ok or r.error
        with pytest.raises(pl.TacticError):
            s.verify()

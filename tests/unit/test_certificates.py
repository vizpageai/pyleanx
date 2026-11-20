"""The certifier slot of the justification engine, and the ring certifier (no Lean)."""

from __future__ import annotations

import warnings

import pytest

import pyleanx as pl
from pyleanx import justify
from pyleanx.render.lean import render_module

x, y = pl.symbols("x y", pl.Real)


def _thm(goal=None, hyps=None, name="h3") -> pl.Theorem:
    hyps = hyps or {"h1": x == 2, "h2": y == x ** 2}
    goal = goal if goal is not None else y == 4
    return pl.Theorem("t", [x, y], assumptions=hyps, conclusion=goal, proof=pl.proof(
        pl.claim(goal, because=list(hyps), name=name), pl.conclude(because=name)))


@pytest.fixture
def certifier():
    """Register a recording certifier for one test."""
    seen: list[justify.Goal] = []

    def certify(goal: justify.Goal) -> str:
        seen.append(goal)
        return "exact CERTIFICATE"

    justify.register_certifier("test", certify, imports=("Test.Module",))
    try:
        yield seen
    finally:
        justify.unregister_certifier("test")


def test_a_certificate_is_tried_before_the_rules(certifier):
    src = render_module([_thm()]).source
    proof = src[src.index("theorem t"):]
    assert proof.index("exact CERTIFICATE") < proof.index("assumption")
    assert "import Test.Module" in src


def test_a_certifier_sees_the_step_and_the_statements_it_cites(certifier):
    render_module([_thm()])
    goal = certifier[0]
    assert goal.statement.same_structure(y == 4)
    assert [n for n, _ in goal.given] == ["h1", "h2"]
    assert goal.given[1][1].same_structure(y == x ** 2)
    assert goal.facts == ("h1", "h2")


def test_a_step_sees_its_scope_not_a_later_step_of_the_same_name(certifier):
    # the claim reuses the hypothesis' name: the certifier must see the hypothesis
    render_module([_thm(goal=y == 4, hyps={"h": y == 4}, name="h")])
    (name, stmt), = certifier[0].given
    assert name == "h" and stmt.same_structure(y == 4)
    render_module([_thm(goal=x == 2, hyps={"h": y == x ** 2, "k": x == 2}, name="h")])
    claim = next(g for g in certifier if g.facts == ("h", "k"))
    assert dict(claim.given)["h"].same_structure(y == x ** 2)
    # the conclusion comes after the claim: there, `h` is the claim
    concl = [g for g in certifier if g.facts == ("h",)][-1]
    assert dict(concl.given)["h"].same_structure(x == 2)


def test_conclusions_and_auto_know_their_goal(certifier):
    render_module([_thm()])
    concl = certifier[-1]
    assert concl.statement.same_structure(y == 4) and concl.facts == ("h3",)
    assert {n for n, _ in concl.context} == {"h1", "h2", "h3"}
    certifier.clear()
    auto = pl.Theorem("a", [x, y], assumptions={"h1": x == 2}, conclusion=x + 1 == 3,
                      proof=pl.auto())
    src = render_module([auto]).source
    (g,) = certifier
    assert g.statement.same_structure(x + 1 == 3) and g.given == ()
    assert g.usable == g.context and dict(g.context)["h1"].same_structure(x == 2)
    assert src.index("exact CERTIFICATE") < src.index("ring1")


def test_goal_is_unknown_after_a_step_that_changes_it(certifier):
    thm = pl.Theorem(
        "f", [x], assumptions={"hx": x > 0}, conclusion=pl.Forall(y, pl.Implies(y > x, y > 0)),
        proof=pl.proof(pl.fix(y, assume={"hy": y > x}), pl.conclude(because=["hx", "hy"])))
    render_module([thm])
    assert certifier == []        # after `fix`, the goal is not tracked: no certifier call


def test_certifiers_can_reduce_a_goal_to_another():
    calls = []

    def outer(goal):
        if goal.depth == 0:
            return [f"(refine ?_; {t})" for t in goal.certify(goal.statement)]
        return None

    def inner(goal):
        calls.append(goal.depth)
        return "exact INNER" if goal.depth > 0 else None

    justify.register_certifier("outer", outer)
    justify.register_certifier("inner", inner, priority=1)
    try:
        assert ("outer", "(refine ?_; exact INNER)") in _thm().derivation().certificates("h3")
        assert 1 in calls
    finally:
        justify.unregister_certifier("outer")
        justify.unregister_certifier("inner")


def test_chain_links_get_certificates(certifier):
    thm = pl.Theorem("c", [x, y], assumptions={"h": x == y}, conclusion=x + 1 == y + 1,
                     proof=pl.proof(pl.chain(x + 1, ("=", y + 1, "h"))))
    render_module([thm])
    assert certifier and certifier[0].statement.same_structure(x + 1 == y + 1)


def test_without_certifiers_the_lean_is_unchanged():
    before = render_module([_thm()]).source

    justify.register_certifier("none", lambda _g: None)
    try:
        assert render_module([_thm()]).source == before
    finally:
        justify.unregister_certifier("none")


def test_a_failing_certifier_warns_and_the_proof_still_renders():
    def broken(_g):
        raise ZeroDivisionError("boom")

    justify.register_certifier("broken", broken)
    try:
        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter("always")
            src = render_module([_thm()]).source
        assert "assumption" in src
        assert any("certifier core:broken failed" in str(m.message) for m in w)
    finally:
        justify.unregister_certifier("broken")


def test_derivation_lists_certificates(certifier):
    assert _thm().derivation().certificates("h3") == [("test", "exact CERTIFICATE")]


def test_pack_certifiers_need_their_pack():
    with pytest.raises(ValueError, match="register the pack"):
        justify.register_certifier("x", lambda g: None, pack="no-such-pack")

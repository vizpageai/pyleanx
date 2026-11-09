"""LLM proposer, arithmetic tactic parsing, LaTeX goal display (no Lean needed)."""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import agent
from pyleanx.agent.parse import TacticParser
from pyleanx.render.goal_latex import goal_to_latex, lean_to_latex


def test_parse_tactics_from_model_replies():
    reply = ("Here are ideas:\n```lean\n1. nlinarith [sq_nonneg (a - b)]\n- positivity\n"
             "sorry\nnative_decide\nset_option maxHeartbeats 0 in simp\n-- comment\n"
             "positivity\n```\n")
    assert agent.parse_tactics(reply) == ["nlinarith [sq_nonneg (a - b)]", "positivity"]
    assert agent.parse_tactics("linarith\nring", k=1) == ["linarith"]


def test_llm_proposer_builds_prompt_and_survives_failures():
    seen = {}

    def complete(prompt):
        seen["prompt"] = prompt
        return "```lean\nlinarith\n```"

    p = agent.LLMProposer(complete, hints=lambda goal: ["two_mul_le_add_sq : 2*a*b ≤ a^2+b^2"])
    obs = {"goals": ["a b : ℝ\n⊢ 2 * a * b ≤ a ^ 2 + b ^ 2"], "history": ["intro h"]}
    assert p(obs) == ["linarith"]
    assert "⊢ 2 * a * b" in seen["prompt"] and "two_mul_le_add_sq" in seen["prompt"]
    assert "intro h" in seen["prompt"] and p.calls == 1

    def broken(prompt):
        raise RuntimeError("rate limited")

    assert agent.LLMProposer(broken)(obs) == []
    assert agent.LLMProposer(complete)({"goals": []}) == []


def test_arithmetic_hints_parse_into_typed_terms():
    a, b = pl.symbols("a b", pl.Real)
    p = TacticParser(scope={"a": a, "b": b})
    t = p("nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]")
    assert type(t).__name__ == "Nlinarith" and str(t) == "nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]"
    assert type(p("use a ^ 2 + 1")).__name__ == "Use"
    assert type(p("aesop")).__name__ == "Aesop" and type(p("exact?")).__name__ == "LibrarySearch"
    for bad in ["nlinarith [sq_nonneg (__import__('os'))]", "use c + 1",
                "nlinarith [sq_nonneg (a.real)]", "use (lambda: 1)()"]:
        with pytest.raises(pl.TacticError):
            p(bad)  # not structured, and raw text is not allowed here


def test_goal_latex():
    tex = goal_to_latex("a x : ℝ\nha : 0 < a\n⊢ 0 < a * x ^ 2 + a")
    assert tex.startswith(r"\begin{array}{l}") and r"a, x : \mathbb{R}" in tex
    assert r"\vdash\ 0 < a \cdot x ^{2} + a" in tex
    assert lean_to_latex("1 ≤ √(1 + ‖v‖ ^ 2)") == r"1 \le \sqrt{1 + \lVert v \rVert ^{2}}"
    assert r"\exp x" in lean_to_latex("Real.exp x ≥ x + 1")
    wrapped = goal_to_latex("h : a +\n    b = c\n⊢ True")
    assert "a + b = c" in wrapped
    assert goal_to_latex("") == r"\begin{array}{l}\end{array}"

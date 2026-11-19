"""Fast feedback without Lean: numeric sanity checks, failure explanations, REPL splitting."""

from __future__ import annotations

import sys
from pathlib import Path

import pyleanx as pl
from pyleanx.backend.interface import Diagnostic, Status, VerificationResult

EXAMPLES = Path(__file__).resolve().parents[2] / "examples"
x, y = pl.symbols("x y", pl.Real)


def test_sanity_check_finds_a_false_step_with_numbers():
    thm = pl.Theorem("b", [x, y], assumptions={"hx": x > 0},
                     conclusion=abs(x + y) <= abs(x) + abs(y),
                     proof=pl.proof(pl.claim(abs(x + y) <= abs(x), name="h1"), pl.conclude()))
    rep = thm.sanity_check()
    assert not rep.ok and "Step 1 looks false" in str(rep) and "the left side is" in str(rep)


def test_sanity_check_finds_a_false_statement():
    thm = pl.Theorem("f", [x], conclusion=x ** 2 > x, proof=pl.proof(pl.conclude()))
    assert "The statement looks false" in str(thm.sanity_check())


def test_sanity_check_is_silent_on_a_correct_proof():
    thm = pl.Theorem("g", [x, y], assumptions={"hx": x > 0, "hy": y > 0},
                     conclusion=(x + y) ** 2 >= 4 * x * y,
                     proof=pl.proof(pl.claim((x - y) ** 2 >= 0, name="h1"),
                                    pl.claim((x + y) ** 2 - 4 * x * y == (x - y) ** 2, name="h2"),
                                    pl.conclude(because=["h1", "h2"])))
    rep = thm.sanity_check()
    assert rep.ok and rep.samples > 0 and "not a proof" in str(rep)


def test_sanity_check_stops_at_proof_by_contradiction():
    thm = pl.Theorem("c", [x], assumptions={"hx": x > 0}, conclusion=x > 0,
                     proof=pl.proof(pl.suppose_not(name="hn"),
                                    pl.claim(x <= 0, because="hn", name="h"),
                                    pl.conclude(because=["hx", "h"])))
    assert thm.sanity_check().ok


def test_explain_failure_names_the_step_and_the_goal():
    thm = pl.Theorem("e", [x, y], assumptions={"hx": x > 0},
                     conclusion=x * y >= 0,
                     proof=pl.proof(pl.claim(x * y >= 0, because="hx", name="h1"),
                                    pl.conclude(because="h1")))
    res = VerificationResult(theorem="e", status=Status.REJECTED, diagnostics=[Diagnostic(
        "error", "linarith failed to find a contradiction\nx y : ℝ\nhx : x > 0\n⊢ False",
        span_kind="tactic", span_label="step 1: have h1 : x * y ≥ 0 := by")])
    why = pl.explain_failure(thm, res, sanity=False)
    assert why and why[0].startswith("Step 1, “xy ≥ 0” (by x > 0 (hx))") and "Still to show: False" in why[0]
    assert "not a linear consequence" in why[0]
    assert "• Step 1" in str(thm.prose(res))


def test_repl_check_splits_imports_preamble_and_theorems():
    sys.path.insert(0, str(EXAMPLES))
    try:
        import pythagoras_similar as ps
    finally:
        sys.path.remove(str(EXAMPLES))
    from pyleanx.backend.repl_check import split_module
    from pyleanx.render.lean import render_module

    m = render_module(ps.THEOREMS)
    c = split_module(m)
    lines = m.source.splitlines()
    pre = "\n".join(lines[c.preamble[0] - 1:c.preamble[1]])
    main = "\n".join(lines[c.main[0] - 1:c.main[1]])
    assert "theorem PyLeanX.Geometry.altitude_to_hypotenuse" in pre and "leg_rule" not in pre
    # the theorems' justification macros belong to them, not to the cached preamble
    assert main.lstrip().startswith("set_option hygiene false in\nmacro \"pyleanx_")
    assert "theorem leg_rule" in main and "#print axioms pythagoras" in main
    assert "pyleanx_s_" not in pre
    assert all(o.startswith("set_option") for o in c.options) and "import" not in pre


def test_because_accepts_a_description_of_the_fact():
    from pyleanx import geometry as geo

    A, B, C, D = geo.points("A B C D")
    c = pl.claim(geo.similar((B, A, C), (C, A, D)), because=["AA similarity", "hABC"])
    assert c.facts[0].name == "EuclideanGeometry.similar_of_angle_angle"
    assert c.facts[1].name == "hABC"
    assert pl.fact("the angles of a triangle add up to 180°").name.endswith(
        "angle_add_angle_add_angle_eq_pi")


def test_an_unclear_description_lists_the_candidates():
    import pytest

    with pytest.raises(pl.TacticError, match="could mean several facts"):
        pl.fact("isosceles triangle")
    assert pl.search_facts("segment addition")[0][1] == "geo.segment_addition"


def test_a_failed_step_without_a_reason_gets_suggestions():
    from pyleanx import geometry as geo
    from pyleanx.diagnose import suggest_facts

    assert any("similar_AA" in s for s in suggest_facts("△BAC ∼ △CAD"))
    A, B, C = geo.points("A B C")
    assert geo  # domain loaded


def test_notebook_display_of_explanations_and_sanity_reports():
    thm = pl.Theorem("nb", [x, y], assumptions={"hx": x > 0}, conclusion=x * y >= 0,
                     proof=pl.proof(pl.claim(x * y >= 0, because="hx", name="h1"),
                                    pl.conclude(because="h1")))
    res = VerificationResult(theorem="nb", status=Status.REJECTED, diagnostics=[Diagnostic(
        "error", "linarith failed\n⊢ False", span_kind="tactic",
        span_label="step 1: have h1 : x * y ≥ 0 := by")])
    md = thm.prose(res).to_markdown()
    assert "\n- Step 1" in md and "    •" not in md  # a list, not an indented code block
    assert thm.sanity_check()._repr_markdown_().startswith("❌ The statement looks false")


def test_a_grind_failure_is_explained_without_its_search_dump():
    from pyleanx.diagnose import _goal, _hint

    msg = ("grind failed\n⊢ False\n[grind] Goal diagnostics\n  [facts] Asserted facts\n"
           "    [prop] dist A B = dist A C\n    [prop] ¬Congruent ![B, M, A] ![C, M, A]")
    assert _goal(msg) == ""
    assert "no automatic justification closed the step" in _hint(msg)
    assert _goal("unsolved goals\nx : ℝ\n⊢ x ≤ x + 1") == "x ≤ x + 1"


def test_a_function_value_times_a_variable_is_written_with_a_dot():
    from pyleanx import analysis as an
    from pyleanx.prose import plain

    x = pl.symbol("x", pl.Real)
    assert plain(an.cos(x) * x) == "cos x · x"          # not "cos xx"
    assert plain(an.sin(x) * an.cos(x)) == "sin x cos x"
    assert plain(2 * x) == "2x"

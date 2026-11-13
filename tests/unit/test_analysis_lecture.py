"""The real-analysis lecture helpers: statements, solutions, figures (no Lean here)."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

EXAMPLES = Path(__file__).resolve().parents[2] / "examples"


@pytest.fixture(scope="module")
def lecture():
    sys.path.insert(0, str(EXAMPLES))
    try:
        import analysis_lecture

        yield analysis_lecture
    finally:
        sys.path.remove(str(EXAMPLES))


def test_solutions_render_as_book_proofs(lecture):
    sols = lecture.all_solutions()
    assert len(sols) == 8
    for thm in sols:
        src = thm.to_lean()
        assert "sorry" not in src and thm.name in src
        assert "∎" in str(thm.prose())
    text = str(lecture.solution("linear_continuous").prose())
    assert "Take δ = ε/3; then ε/3 > 0." in text
    assert "Theorem (one_over_n_tends_to_zero). 1/(n + 1) → 0." in str(
        lecture.solution("one_over_n").prose())
    for build in lecture.EXERCISES.values():
        assert build().proof is None


def test_figures(lecture):
    svg, note = lecture.figure_sequence(0.1)
    assert svg.startswith("<svg") and "N = 10" in svg and "every term from" in note
    svg, note = lecture.figure_eps_delta(0.6, 1.0)
    assert svg.startswith("<svg") and "δ = ε/3 = 0.200" in note
    for svg in (lecture.figure_ivt(), lecture.figure_two_limits()):
        assert svg.startswith("<svg") and "nan" not in svg


def test_notebook_uses_helper_names(lecture):
    nb = json.loads((EXAMPLES / "lecture_real_analysis.ipynb").read_text(encoding="utf-8"))
    code = "\n".join("".join(c["source"]) for c in nb["cells"] if c["cell_type"] == "code")
    for name in ("check", "one_over_n", "limits_unique", "linear_continuous", "exercise_1",
                 "exercise_4", "eps_N", "eps_delta", "explore_sequence", "figure_ivt"):
        assert name in code and hasattr(lecture, name)

"""The lecture notebook's helper module: figures, exercises, solutions (no Lean here)."""

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
        import geometry_lecture

        yield geometry_lecture
    finally:
        sys.path.remove(str(EXAMPLES))


def test_figures_are_svg_and_match_the_givens(lecture):
    for fig in (lecture.figure_kite(), lecture.figure_isosceles(), lecture.figure_bowtie(),
                lecture.figure_shared_side(), lecture.figure_isosceles_right()):
        assert fig.startswith("<svg") and fig.endswith("</svg>") and "nan" not in fig
    k = lecture.kite_points(40, 3)
    assert lecture.measure_angle(k, "B", "A", "C") == pytest.approx(
        lecture.measure_angle(k, "D", "A", "C"))
    assert lecture.measure_dist(k, "B", "C") == pytest.approx(lecture.measure_dist(k, "D", "C"))
    s = lecture.shared_side_points(45, 70)
    assert lecture.measure_angle(s, "A", "B", "C") == pytest.approx(45)
    assert lecture.measure_angle(s, "B", "C", "A") == pytest.approx(70)
    assert lecture._names("ABC'") == ["A", "B", "C'"]


def test_solutions_render_and_exercises_start_empty(lecture):
    sols = lecture.all_solutions()
    assert len(sols) == 6
    for thm in sols:
        src = thm.to_lean()
        assert "sorry" not in src and thm.name in src
        assert "Proof." in str(thm.prose())
    for build in lecture.EXERCISES.values():
        assert build().proof is None


def test_notebook_cells_use_only_helper_names(lecture):
    nb = json.loads((EXAMPLES / "lecture_congruent_triangles.ipynb").read_text(encoding="utf-8"))
    code = "\n".join("".join(c["source"]) for c in nb["cells"] if c["cell_type"] == "code")
    for name in ("show", "draw", "check", "kite", "isosceles_median", "exercise_1",
                 "exercise_4", "explore_kite", "figure_isosceles_right"):
        assert name in code and hasattr(lecture, name)

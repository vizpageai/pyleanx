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


def test_products_of_lengths_print_with_a_dot():
    import pyleanx as pl
    from pyleanx import geometry as geo

    A, B, C = geo.points("A B C")
    t = pl.Theorem("t", [A, B, C],
                   conclusion=geo.dist(A, B) * geo.dist(A, C) == geo.dist(A, C) * geo.dist(A, B))
    assert "|AB| · |AC|" in str(t.prose())


def test_pythagoras_from_similar_triangles_renders():
    import sys
    from pathlib import Path

    examples = Path(__file__).resolve().parents[2] / "examples"
    sys.path.insert(0, str(examples))
    try:
        import pythagoras_similar as ps
    finally:
        sys.path.remove(str(examples))
    src = ps.pythagoras.to_lean()
    prose = str(ps.pythagoras.prose())
    assert "sorry" not in src and "PyLeanX.Geometry.proportional_sides" in src
    # it must not cite Mathlib's Pythagoras (that would be circular)
    assert "dist_sq_eq_dist_sq_add_dist_sq" not in src
    assert "△BAC ∼ △CAD" in str(ps.leg_rule.prose()) and "|AC|² + |BC|² = |AB|²" in prose
    # the altitude is constructed in the proof, not assumed
    assert "theorem PyLeanX.Geometry.altitude " in src and len(ps.pythagoras.assumptions) == 2


def test_perpendicular_lines_and_points_on_a_line():
    import pyleanx as pl
    from pyleanx import geometry as geo

    A, B, C, D = geo.points("A B C D")
    t = pl.Theorem("t", [A, B, C, D], assumptions={"h": geo.on_line(D, geo.line(A, B))},
                   conclusion=geo.perpendicular(geo.line(C, D), geo.line(A, B)))
    assert "D lies on line AB" in str(t.prose()) and "CD ⊥ AB" in str(t.prose())
    assert "Submodule.IsOrtho (AffineSubspace.direction" in t.to_lean()


def test_pythagoras_proof_is_short():
    import sys
    from pathlib import Path

    examples = Path(__file__).resolve().parents[2] / "examples"
    sys.path.insert(0, str(examples))
    try:
        import pythagoras_similar as ps
    finally:
        sys.path.remove(str(examples))
    prose = str(ps.pythagoras.prose())
    assert "the leg rule at A" in prose and "similarly, with A and B exchanged" in prose
    assert "  6." not in prose  # five steps
    assert "  3." not in str(ps.leg_rule.prose())  # two steps

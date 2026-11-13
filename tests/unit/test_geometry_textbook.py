"""The high-school geometry catalogue and the textbook example proofs (no Lean)."""

from __future__ import annotations

import runpy
from pathlib import Path

import pytest

import pyleanx as pl
from pyleanx import geometry as geo
from pyleanx.proofs import LibraryFact, Name
from pyleanx.serialize import theorem_from_canonical

EXAMPLES = Path(__file__).resolve().parents[2] / "examples"
CHAPTERS = {
    "angles": ["angle_comm", "vertical_angles", "linear_pair", "straight_angle",
               "angle_addition"],
    "triangles": ["angle_sum", "exterior_angle", "isosceles_base_angles",
                  "isosceles_converse", "larger_side_larger_angle", "distinct_ab"],
    "congruence": ["sss", "sas", "asa", "aas", "hl", "cpctc_ab", "cpctc_angle_b"],
    "similarity": ["similar_AA", "similar_SAS", "similar_SSS", "similar_angles",
                   "similar_sides"],
    "parallels": ["alternate_angles", "cointerior_angles", "corresponding_angles",
                  "parallel_trans"],
    "right triangles": ["pythagoras_iff", "law_of_cosines", "law_of_sines"],
    "midpoints": ["midpoint_equal_halves", "midpoint_half", "midsegment_parallel",
                  "midsegment_length", "median_to_base_is_perpendicular",
                  "perpendicular_bisector"],
    "circles": ["thales", "intersecting_chords"],
    "quadrilaterals": ["parallelogram_diagonal_sides"],
}


def _body(src: str) -> str:
    return "\n".join(ln for ln in src.splitlines() if not ln.startswith("import "))


@pytest.mark.parametrize("chapter", sorted(CHAPTERS))
def test_every_chapter_has_its_facts_with_labels(chapter: str) -> None:
    for name in CHAPTERS[chapter]:
        fact = getattr(geo, name)
        assert isinstance(fact, Name), name
        assert fact.label, f"{name} needs a plain-language label"
        assert name in geo.LEMMAS


def test_shipped_facts_carry_proofs() -> None:
    shipped = [f for f in geo.LEMMAS.values() if isinstance(f, LibraryFact)]
    assert len(shipped) >= 17
    for f in shipped:
        assert f.name.startswith("PyLeanX.")
        assert f.lean.startswith(f"theorem {f.name} ")
        assert "sorry" not in f.lean and "admit" not in f.lean


def test_vocabulary_renders_for_lean_and_readers() -> None:
    from pyleanx.prose import plain

    A, B, C, D, M = geo.points("A B C D M")
    cases = [
        (geo.is_midpoint(M, B, C), "M = midpoint Real B C", "M = the midpoint of BC"),
        (geo.opposite_sides(B, D, A, C),
         "AffineSubspace.SOppSide (affineSpan Real (insert A (singleton C))) B D",
         "B, D lie on opposite sides of AC"),
        (geo.right_angle(A, M, B), "EuclideanGeometry.angle A M B = Real.pi / 2", "∠AMB = π/2"),
        (geo.congruent((A, B, C), (D, B, C)), "Congruent (Matrix.vecCons A", "△ABC ≅ △DBC"),
    ]
    for expr, lean, text in cases:
        assert expr.to_lean().startswith(lean)
        assert plain(expr) == text
    assert "AB ∥ CD ∧ CB ∥ AD" in plain(geo.parallelogram(A, B, C, D))


def _examples() -> list[pl.Theorem]:
    return runpy.run_path(str(EXAMPLES / "textbook_geometry.py"))["THEOREMS"]


def test_textbook_examples_build_and_round_trip() -> None:
    thms = _examples()
    assert len(thms) == 5
    for thm in thms:
        src = thm.to_lean()
        assert "sorry" not in src
        assert _body(theorem_from_canonical(thm.canonical()).to_lean()) == _body(src)


def test_textbook_examples_read_like_a_textbook() -> None:
    by_name = {t.name: str(t.prose()) for t in _examples()}
    text = by_name["isosceles_median_perpendicular"]
    assert "2. △BMA ≅ △CMA.  (SSS: BM = CM, MA = MA, AB = AC)" in text
    assert "(corresponding parts of congruent triangles (CPCTC))" in text
    assert "(angles on a straight line add up to 180°)" in text
    text = by_name["parallelogram_opposite_sides_equal"]
    assert "6. ∠BAC = ∠ACD.  (alternate interior angles, AB ∥ CD)" in text
    assert "12. △BAC ≅ △DCA.  (ASA)" in text
    text = by_name["angle_in_semicircle"]
    assert "(Pythagoras' theorem (and its converse))" in text
    text = by_name["medial_triangle_half_perimeter"]
    assert "(midsegment of triangle CBA)" in text


def test_gap_filler_reorders_vertices_and_projects_conjunctions() -> None:
    from pyleanx.proofs import Justify

    alts = Justify((Name("h"),)).alternatives()
    assert any(a.startswith("(convert h using 2; ext;") for a in alts)
    assert "exact h.2.1" in alts and "exact (h).symm" in alts

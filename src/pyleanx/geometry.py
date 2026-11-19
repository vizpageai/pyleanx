"""Euclidean plane geometry: points of ℝ², distances and unoriented angles.

    from pyleanx import geometry as geo
    A, B, C = geo.points("A B C")
    pl.Theorem("tri_ineq", [A, B, C],
               conclusion=geo.dist(A, C) <= geo.dist(A, B) + geo.dist(B, C),
               proof=pl.exact(geo.dist_triangle(A, B, C)))

Abstractions and limitations
----------------------------
* ``Point`` is the concrete plane ``EuclideanSpace ℝ (Fin 2)``. Mathlib states most
  geometry for an arbitrary Euclidean affine space ``P`` over a real inner product
  space ``V`` (typeclass binders); PyLeanX instantiates those results at ℝ², so every
  theorem here is a statement about the plane only, not the general one.
* ``angle(A, B, C)`` is Mathlib's unoriented angle ``∠ A B C`` at ``B``, valued in
  ``[0, π]``; for degenerate inputs (``A = B``) Mathlib defines it as ``π / 2``.
* Points support ``=`` and ``≠``; ``line``, ``parallel``, ``on_segment``, ``collinear``,
  ``triangle`` and ``similar`` are Mathlib's notions (affine spans, ``Wbtw``,
  ``Collinear``, ``Similar``). No coordinates, circles or oriented angles yet.
* Textbook facts Mathlib lacks in citable form (``corresponding_angles``,
  ``similar_sides``) are shipped as Lean theorems with proofs; every Lean file that
  cites one contains its proof, so Lean re-checks it each time.
* ``LEMMAS`` reference declarations at :data:`VERIFIED_MATHLIB`; Lean checks every use.
"""

from __future__ import annotations

from collections.abc import Iterable
from typing import Any

from ._domain import CATALOG_VERSION, VERIFIED_MATHLIB, collect_lemmas, lemma
from ._origin import caller_origin
from .errors import ScopeError
from .expr import App, Expr, Func, Var, make_var
from .proofs import library_fact
from .types import Real, Sort, register_sort

_PLANE = "Mathlib.Analysis.InnerProductSpace.PiL2"
_ANGLE = "Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine"
_TRIANGLE = "Mathlib.Geometry.Euclidean.Triangle"
_RIGHT = "Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle"
_METRIC = "Mathlib.Topology.MetricSpace.Pseudo.Defs"

Point = register_sort(Sort(
    "Point", "EuclideanSpace Real (Fin 2)", numeric=False, rank=-1, imports=(_PLANE,),
    unicode="EuclideanSpace ℝ (Fin 2)", latex=r"\mathbb{R}^2"))

_DIST = Func("dist", (Point, Point), Real, (_PLANE,), latex=r"\lvert {0}{1} \rvert")
_ANGLE_F = Func("EuclideanGeometry.angle", (Point, Point, Point), Real, (_ANGLE,),
                latex=r"\angle {0}{1}{2}")


def point(name: str) -> Var:
    return make_var(name, Point, caller_origin())


# -------------------------------------------------------------------------------------
# Justification rules of plane geometry (see pyleanx.justify): what a textbook leaves
# implicit. They apply only to theorems about points.
# -------------------------------------------------------------------------------------
from . import _geometry_numeric  # noqa: E402, F401 - points in the numeric sanity check
from . import justify as _j  # noqa: E402

_j.register_pack("geometry", sorts={"Point"})
# the vertices of a triangle are distinct (from ¬Collinear {A, B, C}), in either order
_DISTINCT = tuple(f"(with_reducible exact {e})" for n in ("ne₁₂", "ne₁₃", "ne₂₃")
                  for e in (f"{n}_of_not_collinear ‹_›", f"({n}_of_not_collinear ‹_›).symm"))
for _slot in ("close", "cheap_close"):
    _j.add_rule(_slot, 30, _DISTINCT, pack="geometry", name=f"{_slot}:distinct vertices")
    # "D strictly between A and B" gives "D weakly between A and B"
    _j.add_rule(_slot, 60, "exact Sbtw.wbtw ‹_›", pack="geometry", name=f"{_slot}:sbtw")
# ∠ACB = ∠BCA; "between A and B" = "between B and A"; triangle ABC = triangle BAC
_j.add_rule("close", 120, "(rw [EuclideanGeometry.angle_comm]; assumption)", pack="geometry",
            name="close:angle symmetric")
_j.add_rule("close", 130, "(apply sbtw_comm.mp; assumption)", pack="geometry",
            name="close:between symmetric")
_j.add_rule("close", 140, "(convert ‹¬ Collinear ℝ _› using 2; ext; simp only "
            "[Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)", pack="geometry",
            name="close:triangle vertex order")
# ∠ABC = ∠CBA and |AB| = |BA|, as in any textbook
_j.add_rule("step", 55, lambda s: [f"(simp only [EuclideanGeometry.angle_comm] at *; "
                                   f"linarith{s.h})"],
            pack="geometry", name="angles up to orientation")
_j.add_rule("step", 230, "(simp only [dist_comm] at *; first | assumption | linarith | ring1 | "
            "(simp_all; done))", pack="geometry", name="distances up to orientation")


def points(names: str | Iterable[str]) -> tuple[Var, ...]:
    """``A, B, C = geo.points("A B C")``."""
    parts = names.replace(",", " ").split() if isinstance(names, str) else list(names)
    if not parts:
        raise ScopeError("points() needs at least one name")
    origin = caller_origin()
    return tuple(make_var(n, Point, origin) for n in parts)


def dist(a: object, b: object) -> App:
    """Euclidean distance ``dist a b`` (a Real)."""
    return _DIST(a, b)


def angle(a: object, b: object, c: object) -> App:
    """Unoriented angle ``∠ a b c`` at vertex ``b``, in radians."""
    return _ANGLE_F(a, b, c)


dist_comm = lemma("dist_comm", _METRIC)
dist_triangle = lemma("dist_triangle", _METRIC,
                       label="the triangle inequality AC ≤ AB + BC")
dist_nonneg = lemma("dist_nonneg", _METRIC,
                     label="distances are nonnegative")
dist_self = lemma("dist_self", _METRIC,
                   label="the distance from a point to itself is 0")
angle_comm = lemma("EuclideanGeometry.angle_comm", _ANGLE)
angle_nonneg = lemma("EuclideanGeometry.angle_nonneg", _ANGLE,
                      label="angles are nonnegative")
angle_le_pi = lemma("EuclideanGeometry.angle_le_pi", _ANGLE,
                     label="an angle is at most 180°")
#: ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π, given p₂ ≠ p₁ (explicit argument p₃).
angle_add_angle_add_angle_eq_pi = lemma("EuclideanGeometry.angle_add_angle_add_angle_eq_pi",
                                        _TRIANGLE,
                                        label="the angles of a triangle add up to 180°")
#: Pythagoras (both directions): |p₁p₃|² = |p₁p₂|² + |p₃p₂|²  ↔  ∠ p₁ p₂ p₃ = π / 2.
pythagoras_iff = lemma(
    "EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two", _RIGHT,
    label="Pythagoras' theorem (and its converse)")

# ---------------------------------------------------------------------------------------
# Lines, segments, triangles and similarity (Mathlib's notions, written as a textbook does)
# ---------------------------------------------------------------------------------------

_AFFINE = "Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic"
_BETWEEN = "Mathlib.Analysis.Convex.Between"
_COLLINEAR = "Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional"
_SIMILAR = "Mathlib.Geometry.Euclidean.Similarity"
_VEC = "Mathlib.Data.Fin.VecNotation"


def _c(name: str, imports: tuple[str, ...], latex: str) -> Any:
    from .terms import const

    return const(name, imports=imports, latex=latex)


def _set(*pts: object) -> Any:
    """``{A, B, C}`` as Lean elaborates it (``insert A (insert B (singleton C))``)."""
    from .terms import apply

    out = apply(_c("singleton", (), "{0}"), pts[-1])
    for p in reversed(pts[:-1]):
        out = apply(_c("insert", (), "{0}{1}"), p, out)
    return out


def _vec(*pts: object) -> Any:
    """``![A, B, C]``."""
    from .terms import apply

    out: Any = _c("Matrix.vecEmpty", (_VEC,), " ")
    for p in reversed(pts):
        out = apply(_c("Matrix.vecCons", (_VEC,), "{0}{1}"), p, out)
    return out


def line(a: object, b: object) -> Any:
    """The line through ``a`` and ``b`` (``line[ℝ, a, b]``, an affine subspace)."""
    from .terms import apply

    return apply(_c("affineSpan", (_AFFINE,), "{1}"), Real, _set(a, b))


def parallel(l1: object, l2: object) -> Expr:
    """``l1 ∥ l2`` for lines (Mathlib's ``AffineSubspace.Parallel``)."""
    from .terms import apply

    return apply(_c("AffineSubspace.Parallel", (_AFFINE,), r"{0} \parallel {1}"), l1, l2)


_ORTHO = "Mathlib.Analysis.InnerProductSpace.Orthogonal"


def perpendicular(l1: object, l2: object) -> Expr:
    """``l1 ⊥ l2`` for lines: their directions are orthogonal (Mathlib's
    ``l1.direction ⟂ l2.direction``)."""
    from .terms import apply

    def direction(ln: object) -> Any:
        return apply(_c("AffineSubspace.direction", (_AFFINE,), "{0}"), ln)

    return apply(_c("Submodule.IsOrtho", (_ORTHO,), r"{0} \perp {1}"), direction(l1),
                 direction(l2))


def on_line(p: object, ln: object) -> Expr:
    """``p`` lies on the line ``ln`` (``p ∈ line[ℝ, a, b]``)."""
    from .terms import apply

    return apply(_c("Membership.mem", (_AFFINE,), r"{1} \text{{ lies on line }} {0}"), ln, p)


def on_segment(p: object, a: object, b: object) -> Expr:
    """``p`` lies on the segment ``ab`` (endpoints allowed; Mathlib's ``Wbtw ℝ a p b``)."""
    from .terms import apply

    return apply(_c("Wbtw", (_BETWEEN,), r"{2} \in \overline{{{1}{3}}}"), Real, a, p, b)


def collinear(*pts: object) -> Expr:
    """The points lie on one line (Mathlib's ``Collinear ℝ {…}``)."""
    from .terms import apply

    return apply(_c("Collinear", (_COLLINEAR,), r"{1} \text{{ collinear}}"), Real, _set(*pts))


def triangle(a: object, b: object, c: object) -> Expr:
    """``a, b, c`` form a (non-degenerate) triangle: they are not collinear."""
    from .expr import Not

    return Not(collinear(a, b, c))


def similar(t1: tuple[object, object, object], t2: tuple[object, object, object]) -> Expr:
    """Triangle ``t1`` is similar to ``t2`` with vertices in this order (``![…] ∼ ![…]``)."""
    from .terms import apply

    return apply(_c("Similar", (_SIMILAR,), r"\triangle {0} \sim \triangle {1}"),
                 _vec(*t1), _vec(*t2))


def congruent(t1: tuple[object, object, object], t2: tuple[object, object, object]) -> Expr:
    """Triangle ``t1`` is congruent to ``t2`` with vertices in this order
    (Mathlib's ``Congruent ![…] ![…]``: all corresponding distances are equal)."""
    from .terms import apply

    return apply(_c("Congruent", (_CONGRUENCE,), r"\triangle {0} \cong \triangle {1}"),
                 _vec(*t1), _vec(*t2))


def midpoint(a: object, b: object) -> Any:
    """The midpoint of segment ``ab`` (Mathlib's ``midpoint ℝ a b``)."""
    from .terms import Const, apply

    c = Const("midpoint", Point, ("Mathlib.LinearAlgebra.AffineSpace.Midpoint",),
              r"\text{{the midpoint of }} {1}{2}", arity=3, result=Point)
    return apply(c, Real, a, b)


def right_angle(a: object, b: object, c: object) -> Expr:
    """``∠abc`` is a right angle (``∠ a b c = π / 2``)."""
    from .analysis import pi

    return angle(a, b, c) == pi() / 2


def on_circle(p: object, center: object, radius: object) -> Expr:
    """``p`` lies on the circle with ``center`` and ``radius`` (``dist p center = radius``)."""
    return dist(p, center) == radius


def parallelogram(a: object, b: object, c: object, d: object) -> Expr:
    """``abcd`` is a parallelogram: a non-degenerate quadrilateral whose opposite sides
    are parallel (``ab ∥ cd``, ``cb ∥ ad``, and ``a, b, c`` not collinear)."""
    from .expr import And

    return And(triangle(a, b, c), parallel(line(a, b), line(c, d)),
               parallel(line(c, b), line(a, d)))


def is_midpoint(m: object, a: object, b: object) -> Expr:
    """``m`` is the midpoint of segment ``ab`` (``m = midpoint ℝ a b``)."""
    from .expr import _compare

    return _compare("eq", m, midpoint(a, b))


def opposite_sides(p: object, q: object, a: object, b: object) -> Expr:
    """``p`` and ``q`` lie on opposite sides of line ``ab`` (strictly; Mathlib's
    ``line[ℝ, a, b].SOppSide p q``)."""
    from .terms import apply

    return apply(_c("AffineSubspace.SOppSide", ("Mathlib.Analysis.Convex.Side",),
                    r"{1}, {2} \text{{ lie on opposite sides of }} {0}"), line(a, b), p, q)


def same_side(p: object, q: object, a: object, b: object) -> Expr:
    """``p`` and ``q`` lie (strictly) on the same side of line ``ab``."""
    from .terms import apply

    return apply(_c("AffineSubspace.SSameSide", ("Mathlib.Analysis.Convex.Side",),
                    r"{1}, {2} \text{{ lie on the same side of }} {0}"), line(a, b), p, q)


def concyclic(*pts: object) -> Expr:
    """The points lie on one circle (Mathlib's ``Cospherical {…}``)."""
    from .terms import apply

    return apply(_c("EuclideanGeometry.Cospherical", ("Mathlib.Geometry.Euclidean.Sphere.Basic",),
                    r"{0} \text{{ lie on a circle}}"), _set(*pts))


_CONGRUENCE = "Mathlib.Geometry.Euclidean.Congruence"

#: AA: two pairs of equal angles (at b and at c) make the triangles similar.
similar_AA = lemma("EuclideanGeometry.similar_of_angle_angle", _SIMILAR,
                   label="AA similarity")

_GEO_FACT_IMPORTS = (_SIMILAR, _ANGLE, _BETWEEN, _AFFINE, _COLLINEAR)
#: D on AB, E on AC, DE ∥ BC  ⟹  ∠ABC = ∠ADE and ∠BCA = ∠DEA (corresponding angles).
#: Cite it for either equality; the gap filler uses the half the claim needs.
corresponding_angles = library_fact(
    "PyLeanX.Geometry.corresponding_angles", """
    theorem PyLeanX.Geometry.corresponding_angles {V P : Type*} [NormedAddCommGroup V]
        [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {A B C D E : P}
        (hABC : ¬ Collinear ℝ {A, B, C}) (hD : Wbtw ℝ A D B) (hE : Wbtw ℝ A E C)
        (hP : (line[ℝ, D, E]).Parallel line[ℝ, B, C]) :
        EuclideanGeometry.angle A B C = EuclideanGeometry.angle A D E ∧
          EuclideanGeometry.angle B C A = EuclideanGeometry.angle D E A := by
      have hC : C ∉ line[ℝ, B, A] := by
        intro h
        apply hABC
        have := collinear_insert_of_mem_affineSpan_pair h
        rwa [Set.insert_comm, Set.pair_comm, Set.insert_comm] at this
      have hEm : E ∈ line[ℝ, C, A] := by rw [Set.pair_comm]; exact hE.mem_affineSpan
      have hdir1 : line[ℝ, E, A].direction ≤ line[ℝ, C, A].direction :=
        AffineSubspace.direction_le
          (affineSpan_pair_le_of_mem_of_mem hEm (right_mem_affineSpan_pair _ _ _))
      have hdir2 : line[ℝ, A, D].direction ≤ line[ℝ, A, B].direction :=
        AffineSubspace.direction_le
          (affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair _ _ _) hD.mem_affineSpan)
      obtain ⟨r, hr, h1, h2, h3⟩ := exists_eq_smul_of_parallel hC hP.symm hdir1 hdir2
      constructor
      · have hAD : A -ᵥ D = r • (A -ᵥ B) := by
          rw [← neg_vsub_eq_vsub_rev D A, h3, ← smul_neg, neg_vsub_eq_vsub_rev]
        simp only [EuclideanGeometry.angle]
        rw [hAD, h1, InnerProductGeometry.angle_smul_smul hr]
      · have hDE : D -ᵥ E = r • (B -ᵥ C) := by
          rw [← neg_vsub_eq_vsub_rev E D, h1, ← smul_neg, neg_vsub_eq_vsub_rev]
        simp only [EuclideanGeometry.angle]
        rw [hDE, h2, InnerProductGeometry.angle_smul_smul hr]
    """, *_GEO_FACT_IMPORTS, label="corresponding angles (DE ∥ BC)")

#: △abc ∼ △a'b'c' (abc a triangle)  ⟹  a'b'/ab = a'c'/ac.
similar_sides = library_fact(
    "PyLeanX.Geometry.similar_sides", """
    theorem PyLeanX.Geometry.similar_sides {V₁ V₂ P₁ P₂ : Type*} [NormedAddCommGroup V₁]
        [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₁] [InnerProductSpace ℝ V₂]
        [MetricSpace P₁] [MetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
        {a b c : P₁} {a' b' c' : P₂} (h : Similar ![a, b, c] ![a', b', c'])
        (hT : ¬ Collinear ℝ {a, b, c}) :
        dist a' b' / dist a b = dist a' c' / dist a c := by
      have hab : a ≠ b := ne₁₂_of_not_collinear hT
      have hac : a ≠ c := ne₁₃_of_not_collinear hT
      obtain ⟨r, hr, hd⟩ := similar_iff_exists_pos_dist_eq.mp h
      have h1 : dist a b = r * dist a' b' := by simpa using hd 0 1
      have h2 : dist a c = r * dist a' c' := by simpa using hd 0 2
      have hb : dist a' b' ≠ 0 := by
        intro h0; apply hab; rw [← dist_eq_zero, h1, h0, mul_zero]
      have hc : dist a' c' ≠ 0 := by
        intro h0; apply hac; rw [← dist_eq_zero, h2, h0, mul_zero]
      rw [h1, h2]
      field_simp
    """, *_GEO_FACT_IMPORTS, label="similar triangles have proportional sides")

# ---------------------------------------------------------------------------------------
# Constructions: extending a side; angle bisectors
# ---------------------------------------------------------------------------------------


def strictly_between(p: object, a: object, b: object) -> Expr:
    """``p`` lies on segment ``ab`` and is neither endpoint (Mathlib's ``Sbtw ℝ a p b``)."""
    from .terms import apply

    return apply(_c("Sbtw", (_BETWEEN,), r"{2} \text{{ lies strictly between }} {1} "
                    r"\text{{ and }} {3}"), Real, a, p, b)


def extend_beyond(b: object, a: object, length: object) -> Any:
    """The point on ray ``ba`` beyond ``a`` whose distance from ``a`` is ``length``
    (``AffineMap.lineMap b a (1 + length / dist a b)``)."""
    from .terms import apply

    t = 1 + length / dist(a, b)
    return apply(_c("AffineMap.lineMap", ("Mathlib.LinearAlgebra.AffineSpace.AffineMap",),
                    r"\text{{the point on ray }} {0}{1} \text{{ beyond }} {1}"), b, a, t)


_BIS = (*_GEO_FACT_IMPORTS, "Mathlib.Analysis.Normed.Affine.AddTorsor",
        "Mathlib.Analysis.Normed.Affine.Convex", "Mathlib.Analysis.InnerProductSpace.Basic",
        "Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic")

#: E on ray BA beyond A (E = extend_beyond(B, A, r))  ⟹  A lies on segment BE.
extension_between = library_fact("PyLeanX.Geometry.extend_wbtw", """
theorem PyLeanX.Geometry.extend_wbtw {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {A B : V} {r : ℝ} (hr : 0 ≤ r) :
    Wbtw ℝ B A (AffineMap.lineMap B A (1 + r)) := by
  have h := wbtw_smul_vadd_smul_vadd_of_nonneg_of_le B (A -ᵥ B) zero_le_one
    (show (1 : ℝ) ≤ 1 + r by linarith)
  simpa [AffineMap.lineMap_apply] using h
""", *_BIS, label="E lies on BA extended beyond A")

#: AE = AC for E = extend_beyond(B, A, dist A C).
extension_length = library_fact("PyLeanX.Geometry.extend_dist", """
theorem PyLeanX.Geometry.extend_dist {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {A B C : V} (hABC : ¬ Collinear ℝ {A, B, C}) :
    dist A (AffineMap.lineMap B A (1 + dist A C / dist A B)) = dist A C := by
  have hAB : dist A B ≠ 0 := dist_ne_zero.2 (ne₁₂_of_not_collinear hABC)
  rw [dist_comm, dist_lineMap_right, dist_comm B A]
  have : ‖(1 : ℝ) - (1 + dist A C / dist A B)‖ = dist A C / dist A B := by
    rw [show (1 : ℝ) - (1 + dist A C / dist A B) = -(dist A C / dist A B) by ring, norm_neg,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [this]
  field_simp
""", *_BIS, label="AE = AC by the construction of E")

#: ABC a triangle, A between B and E  ⟹  B, E, C form a triangle.
extension_triangle = library_fact("PyLeanX.Geometry.extend_triangle", """
theorem PyLeanX.Geometry.extend_triangle {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {A B C E : V} (hABC : ¬ Collinear ℝ {A, B, C}) (hE : Wbtw ℝ B A E) :
    ¬ Collinear ℝ {B, E, C} := by
  intro h
  have hAB : A ≠ B := ne₁₂_of_not_collinear hABC
  have hBE : B ≠ E := by
    rintro rfl
    exact hAB ((wbtw_self_iff ℝ).1 hE)
  have hC : C ∈ line[ℝ, B, E] :=
    h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBE
  have hA : A ∈ line[ℝ, B, E] := hE.mem_affineSpan
  have hB : B ∈ line[ℝ, B, E] := left_mem_affineSpan_pair _ _ _
  exact hABC (collinear_triple_of_mem_affineSpan_pair hA hB hC)
""", *_BIS, label="C is not on line BA, so BEC is a triangle")

#: AD bisects ∠BAC (D strictly between B and C), E on BA beyond A with AE = AC  ⟹  AD ∥ EC.
bisector_parallel = library_fact("PyLeanX.Geometry.bisector_parallel", """
theorem PyLeanX.Geometry.bisector_parallel {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    {A B C D : V} (hABC : ¬ Collinear ℝ {A, B, C}) (hD : Sbtw ℝ B D C)
    (hbis : EuclideanGeometry.angle B A D = EuclideanGeometry.angle D A C) :
    (line[ℝ, A, D]).Parallel line[ℝ, AffineMap.lineMap B A (1 + dist A C / dist A B), C] := by
  have hAB : A ≠ B := ne₁₂_of_not_collinear hABC
  have hAC : A ≠ C := ne₁₃_of_not_collinear hABC
  have hAD : A ≠ D := by
    rintro rfl
    exact hABC (collinear_insert_of_mem_affineSpan_pair hD.wbtw.mem_affineSpan)
  obtain ⟨⟨s, ⟨hs0, hs1⟩, hsD⟩, hDB, hDC⟩ := hD
  have hs : s ≠ 0 := by
    rintro rfl
    exact hDB (by simpa using hsD.symm)
  rw [AffineMap.lineMap_apply] at hsD
  simp only [vsub_eq_sub, vadd_eq_add] at hsD
  -- equal angles: equal cosines
  have hcos := congrArg Real.cos hbis
  simp only [EuclideanGeometry.angle, vsub_eq_sub, InnerProductGeometry.cos_angle] at hcos
  rw [real_inner_comm (C - A) (D - A)] at hcos
  have hd : D - A = (B - A) + s • ((C - A) - (B - A)) := by rw [← hsD]; module
  have hβ : ‖B - A‖ ≠ 0 := by simpa [sub_eq_zero] using hAB.symm
  have hγ : ‖C - A‖ ≠ 0 := by simpa [sub_eq_zero] using hAC.symm
  have hδ : ‖D - A‖ ≠ 0 := by simpa [sub_eq_zero] using hAD.symm
  rw [div_eq_div_iff (mul_ne_zero hβ hδ) (mul_ne_zero hδ hγ)] at hcos
  set b := B - A with hb_def
  set c := C - A with hc_def
  set δ := ‖D - A‖ with hδ_def
  clear_value b c δ
  rw [hd] at hcos
  simp only [inner_add_right, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq,
    real_inner_comm b c] at hcos
  -- strict Cauchy–Schwarz: b and c are not parallel
  have hp : inner ℝ b c ≠ ‖b‖ * ‖c‖ := by
    intro h
    rw [inner_eq_norm_mul_iff_real] at h
    apply hABC
    rw [collinear_iff_of_mem (p₀ := A) (by simp)]
    refine ⟨b, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro p (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [hb_def]⟩
    · refine ⟨‖c‖ / ‖b‖, ?_⟩
      have : c = (‖c‖ / ‖b‖) • b := by
        rw [div_eq_inv_mul, mul_smul, h, smul_smul, inv_mul_cancel₀ hβ, one_smul]
      rw [vadd_eq_add, ← this, hc_def]
      abel
  have key : (1 - s) * ‖b‖ = s * ‖c‖ := by
    have hpos : ‖b‖ * ‖c‖ - inner ℝ b c ≠ 0 := sub_ne_zero.2 (Ne.symm hp)
    have h0 : δ * ((‖b‖ * ‖c‖ - inner ℝ b c) * ((1 - s) * ‖b‖ - s * ‖c‖)) = 0 := by
      linear_combination hcos
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hδ
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hpos
    · linarith
  -- E - C = s⁻¹ • (A - D)
  have hr : s * (dist A C / dist A B) = 1 - s := by
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev A C, norm_sub_rev A B, ← hb_def, ← hc_def]
    field_simp
    linarith [key]
  have hsE : s • (AffineMap.lineMap B A (1 + dist A C / dist A B) -ᵥ C) = A -ᵥ D := by
    rw [AffineMap.lineMap_apply, ← hsD]
    simp only [vsub_eq_sub, vadd_eq_add]
    linear_combination (norm := module) hr • (A - B)
  have hE : AffineMap.lineMap B A (1 + dist A C / dist A B) -ᵥ C = s⁻¹ • (A -ᵥ D) := by
    rw [← hsE, smul_smul, inv_mul_cancel₀ hs, one_smul]
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq, vectorSpan_pair, vectorSpan_pair,
    hE, Submodule.span_singleton_smul_eq (IsUnit.inv (Ne.isUnit hs))]
""", *_BIS, label="△ACE is isosceles (AE = AC), so EC is parallel to the bisector AD")

#: 0 < AB and 0 < AC in a triangle ABC.
triangle_sides_pos = library_fact("PyLeanX.Geometry.triangle_sides_pos", """
theorem PyLeanX.Geometry.triangle_sides_pos {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {A B C : P}
    (hABC : ¬ Collinear ℝ {A, B, C}) : 0 < dist A B ∧ 0 < dist A C :=
  ⟨dist_pos.2 (ne₁₂_of_not_collinear hABC), dist_pos.2 (ne₁₃_of_not_collinear hABC)⟩
""", *_BIS, label="the sides of a triangle have positive length")

#: D strictly between B and C  ⟹  0 < BD and 0 < DC.
between_dist_pos = library_fact("PyLeanX.Geometry.sbtw_dist_pos", """
theorem PyLeanX.Geometry.sbtw_dist_pos {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {B C D : P}
    (hD : Sbtw ℝ B D C) : 0 < dist B D ∧ 0 < dist D C :=
  ⟨dist_pos.2 hD.left_ne, dist_pos.2 hD.ne_right⟩
""", *_BIS, label="a point strictly inside a segment is at positive distance from both ends")

#: Componendo: a/(a + b) = c/(c + d) with b, d > 0 and a, c ≥ 0  ⟹  a/b = c/d.
componendo = library_fact("PyLeanX.Algebra.componendo", """
theorem PyLeanX.Algebra.componendo {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c)
    (hd : 0 < d) (h : a / (a + b) = c / (c + d)) : a / b = c / d := by
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  rw [div_eq_div_iff hb.ne' hd.ne']
  linarith
""", *_BIS, label="componendo: a/(a + b) = c/(c + d) gives a/b = c/d")
dist_add_dist = lemma("Wbtw.dist_add_dist", "Mathlib.Analysis.Normed.Affine.Convex",
                      label="distances add along a segment")

#: Segment addition postulate: D on segment AB  ⟹  AB = AD + DB (D may be strictly between).
segment_addition = library_fact("PyLeanX.Geometry.segment_addition", """
theorem PyLeanX.Geometry.segment_addition {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {A B D : P}
    (hD : Wbtw ℝ A D B) : dist A B = dist A D + dist D B :=
  (hD.dist_add_dist).symm
""", *_BIS, label="segment addition")

#: Flip both ratios: a/b = c/d  ⟹  b/a = d/c.
flip_ratio = library_fact("PyLeanX.Algebra.flip_ratio", """
theorem PyLeanX.Algebra.flip_ratio {a b c d : ℝ} (h : a / b = c / d) : b / a = d / c := by
  rw [← inv_div a b, ← inv_div c d, h]
""", *_BIS, label="flip both ratios")

#: Split a fraction: 0 < a  ⟹  (a + b)/a = 1 + b/a.
split_fraction = library_fact("PyLeanX.Algebra.split_fraction", """
theorem PyLeanX.Algebra.split_fraction {a b : ℝ} (ha : 0 < a) : (a + b) / a = 1 + b / a := by
  rw [add_div, div_self ha.ne']
""", *_BIS, label="split the fraction")

#: Cross-multiplication: a/b = c/d  ⟺  a·d = c·b (for b, d ≠ 0; cite b > 0, d > 0).
cross_multiply = lemma("div_eq_div_iff", "Mathlib.Algebra.Order.Field.Basic",
                       label="cross-multiplication")

#: D strictly between A and B  ⟹  ∠DAC = ∠BAC and ∠DBC = ∠ABC (D is on rays AB and BA).
angle_on_segment = library_fact("PyLeanX.Geometry.angle_on_segment", """
theorem PyLeanX.Geometry.angle_on_segment {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {A B D : P}
    (h : Sbtw ℝ A D B) (C : P) :
    EuclideanGeometry.angle D A C = EuclideanGeometry.angle B A C ∧
      EuclideanGeometry.angle D B C = EuclideanGeometry.angle A B C :=
  ⟨h.angle_eq_left C, (sbtw_comm.mp h).angle_eq_left C⟩
""", *_GEO_FACT_IMPORTS, label="D lies on segment AB, so it is on ray AB and on ray BA")

#: The altitude from C in any triangle ABC, and when its foot lies inside AB.
altitude = library_fact("PyLeanX.Geometry.altitude", """
theorem PyLeanX.Geometry.altitude {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {A B C : P} (hABC : ¬ Collinear ℝ {A, B, C}) :
    ∃ D : P, D ∈ line[ℝ, A, B] ∧ (line[ℝ, C, D]).direction ⟂ (line[ℝ, A, B]).direction := by
  have hAB : A ≠ B := ne₁₂_of_not_collinear hABC
  have hu : 0 < ‖B -ᵥ A‖ := norm_pos_iff.mpr (vsub_ne_zero.mpr hAB.symm)
  have hu' : ‖B -ᵥ A‖ ^ 2 ≠ 0 := pow_ne_zero 2 hu.ne'
  refine ⟨AffineMap.lineMap A B (inner ℝ (C -ᵥ A) (B -ᵥ A) / ‖B -ᵥ A‖ ^ 2),
    AffineMap.lineMap_mem_affineSpan_pair _ _ _, ?_⟩
  rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair, vectorSpan_pair,
    Submodule.isOrtho_span]
  intro u hu v hv
  rw [Set.mem_singleton_iff] at hu hv
  subst hu hv
  rw [AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub, ← neg_vsub_eq_vsub_rev B A]
  simp only [inner_neg_right, inner_sub_left, real_inner_smul_left]
  rw [real_inner_self_eq_norm_sq]
  field_simp
  ring
""", *_GEO_FACT_IMPORTS, _ORTHO,
    label="every triangle has an altitude: a point D on line AB with CD ⊥ AB")

foot_right_angles = library_fact("PyLeanX.Geometry.foot_right_angles", """
theorem PyLeanX.Geometry.foot_right_angles {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {A B C D : P} (hD : D ∈ line[ℝ, A, B])
    (h : (line[ℝ, C, D]).direction ⟂ (line[ℝ, A, B]).direction) :
    EuclideanGeometry.angle A D C = Real.pi / 2 ∧
      EuclideanGeometry.angle B D C = Real.pi / 2 := by
  have hCD : C -ᵥ D ∈ (line[ℝ, C, D]).direction :=
    AffineSubspace.vsub_mem_direction (left_mem_affineSpan_pair _ _ _)
      (right_mem_affineSpan_pair _ _ _)
  have hA : A -ᵥ D ∈ (line[ℝ, A, B]).direction :=
    AffineSubspace.vsub_mem_direction (left_mem_affineSpan_pair _ _ _) hD
  have hB : B -ᵥ D ∈ (line[ℝ, A, B]).direction :=
    AffineSubspace.vsub_mem_direction (right_mem_affineSpan_pair _ _ _) hD
  constructor
  · rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two,
      real_inner_comm]
    exact h.inner_eq hCD hA
  · rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two,
      real_inner_comm]
    exact h.inner_eq hCD hB
""", *_GEO_FACT_IMPORTS, _ORTHO,
    label="CD ⊥ AB at D makes right angles at D")

foot_between = library_fact("PyLeanX.Geometry.foot_between", """
theorem PyLeanX.Geometry.foot_between {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {A B C D : P} (hAB : A ≠ B) (hD : D ∈ line[ℝ, A, B])
    (h : (line[ℝ, C, D]).direction ⟂ (line[ℝ, A, B]).direction)
    (hA : EuclideanGeometry.angle C A B < Real.pi / 2)
    (hB : EuclideanGeometry.angle C B A < Real.pi / 2) : Sbtw ℝ A D B := by
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hD
  have hCD : C -ᵥ AffineMap.lineMap A B t ∈ (line[ℝ, C, AffineMap.lineMap A B t]).direction :=
    AffineSubspace.vsub_mem_direction (left_mem_affineSpan_pair _ _ _)
      (right_mem_affineSpan_pair _ _ _)
  have hBA : B -ᵥ A ∈ (line[ℝ, A, B]).direction :=
    AffineSubspace.vsub_mem_direction (right_mem_affineSpan_pair _ _ _)
      (left_mem_affineSpan_pair _ _ _)
  have h0 := h.inner_eq hCD hBA
  rw [AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at h0
  have hpA : 0 < inner ℝ (C -ᵥ A) (B -ᵥ A) := not_le.mp fun hn =>
    absurd (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mp hn) (not_le.mpr hA)
  have hpB : 0 < inner ℝ (C -ᵥ B) (A -ᵥ B) := not_le.mp fun hn =>
    absurd (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mp hn) (not_le.mpr hB)
  rw [← vsub_sub_vsub_cancel_right C B A, ← neg_vsub_eq_vsub_rev B A, inner_neg_right,
    inner_sub_left, real_inner_self_eq_norm_sq] at hpB
  have hn : 0 < ‖B -ᵥ A‖ ^ 2 := pow_pos (norm_pos_iff.mpr (vsub_ne_zero.mpr hAB.symm)) 2
  have ht0 : 0 < t := by nlinarith
  have ht1 : t < 1 := by nlinarith
  exact sbtw_iff_mem_image_Ioo_and_ne.mpr ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hAB⟩
""", *_GEO_FACT_IMPORTS, _ORTHO,
    label="if the angles at A and B are acute, the foot of the altitude lies strictly "
    "between A and B")

right_triangle_acute = library_fact("PyLeanX.Geometry.right_triangle_acute", """
theorem PyLeanX.Geometry.right_triangle_acute {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {A B C : P} (hABC : ¬ Collinear ℝ {A, B, C})
    (hC : EuclideanGeometry.angle A C B = Real.pi / 2) :
    EuclideanGeometry.angle C A B < Real.pi / 2 ∧
      EuclideanGeometry.angle C B A < Real.pi / 2 := by
  have hAC : A ≠ C := ne₁₃_of_not_collinear hABC
  have hBC : B ≠ C := ne₂₃_of_not_collinear hABC
  have hwz : inner ℝ (A -ᵥ C) (B -ᵥ C) = 0 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mpr hC
  have hzw : inner ℝ (B -ᵥ C) (A -ᵥ C) = 0 := by rw [real_inner_comm]; exact hwz
  have key : ∀ {X Y : P}, inner ℝ (X -ᵥ C) (Y -ᵥ C) = 0 → X ≠ C →
      EuclideanGeometry.angle C X Y < Real.pi / 2 := by
    intro X Y hXY hX
    have hn : 0 < ‖X -ᵥ C‖ := norm_pos_iff.mpr (vsub_ne_zero.mpr hX)
    rw [EuclideanGeometry.angle]
    apply not_le.mp
    rw [← InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle, not_le,
      ← vsub_add_vsub_cancel Y C X, inner_add_right, real_inner_self_eq_norm_sq,
      ← neg_vsub_eq_vsub_rev X C, inner_neg_left, hXY, norm_neg]
    simp only [neg_zero, zero_add]
    exact pow_pos hn 2
  exact ⟨key hwz hAC, key hzw hBC⟩
""", *_GEO_FACT_IMPORTS, _ORTHO,
    label="the other two angles of a right triangle are acute")

#: The altitude from the right angle: in a right triangle (right angle at C) it meets the
#: hypotenuse at a point D strictly between A and B, with right angles at D.
altitude_to_hypotenuse = library_fact("PyLeanX.Geometry.altitude_to_hypotenuse", """
theorem PyLeanX.Geometry.altitude_to_hypotenuse {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {A B C : P} (hABC : ¬ Collinear ℝ {A, B, C})
    (hC : EuclideanGeometry.angle A C B = Real.pi / 2) :
    ∃ D : P, Sbtw ℝ A D B ∧ EuclideanGeometry.angle A D C = Real.pi / 2 ∧
      EuclideanGeometry.angle B D C = Real.pi / 2 := by
  obtain ⟨D, hD, hperp⟩ := PyLeanX.Geometry.altitude hABC
  obtain ⟨hA, hB⟩ := PyLeanX.Geometry.right_triangle_acute hABC hC
  exact ⟨D, PyLeanX.Geometry.foot_between (ne₁₂_of_not_collinear hABC) hD hperp hA hB,
    PyLeanX.Geometry.foot_right_angles hD hperp⟩
""", *_GEO_FACT_IMPORTS, _ORTHO, label="drop the altitude from the right angle to the hypotenuse",
    requires=[altitude, foot_right_angles, foot_between, right_triangle_acute])

#: D on segment AB  ⟹  ∠BAC = ∠CAD (the triangles ABC and ADC share the angle at A).
common_angle = library_fact("PyLeanX.Geometry.common_angle", """
theorem PyLeanX.Geometry.common_angle {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {A B D : P} (h : Sbtw ℝ A D B) (C : P) :
    EuclideanGeometry.angle B A C = EuclideanGeometry.angle C A D := by
  rw [EuclideanGeometry.angle_comm C A D]
  exact (h.angle_eq_left C).symm
""", *_GEO_FACT_IMPORTS, label="D lies on AB, so the angle at A is common")

#: △abc ∼ △a'b'c'  ⟹  b'a'·bc = b'c'·ba (proportional sides from the vertex b, multiplied out).
proportional_sides = library_fact("PyLeanX.Geometry.proportional_sides", """
theorem PyLeanX.Geometry.proportional_sides {V₁ V₂ P₁ P₂ : Type*} [NormedAddCommGroup V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₁] [InnerProductSpace ℝ V₂]
    [MetricSpace P₁] [MetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
    {a b c : P₁} {a' b' c' : P₂} (h : Similar ![a, b, c] ![a', b', c']) :
    dist b' a' * dist b c = dist b' c' * dist b a := by
  obtain ⟨r, hr, hd⟩ := similar_iff_exists_pos_dist_eq.mp h
  have h1 : dist b a = r * dist b' a' := by simpa using hd 1 0
  have h2 : dist b c = r * dist b' c' := by simpa using hd 1 2
  rw [h1, h2]
  ring
""", *_GEO_FACT_IMPORTS, label="corresponding sides of similar triangles are proportional")

#: △abc ∼ △a'b'c' (abc a triangle)  ⟹  b'a'/ba = b'c'/bc: the sides from the vertex b.
similar_sides_at = library_fact("PyLeanX.Geometry.similar_sides_at", """
theorem PyLeanX.Geometry.similar_sides_at {V₁ V₂ P₁ P₂ : Type*} [NormedAddCommGroup V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₁] [InnerProductSpace ℝ V₂]
    [MetricSpace P₁] [MetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
    {a b c : P₁} {a' b' c' : P₂} (h : Similar ![a, b, c] ![a', b', c'])
    (hT : ¬ Collinear ℝ {a, b, c}) :
    dist b' a' / dist b a = dist b' c' / dist b c := by
  have hba : b ≠ a := (ne₁₂_of_not_collinear hT).symm
  have hbc : b ≠ c := ne₂₃_of_not_collinear hT
  obtain ⟨r, hr, hd⟩ := similar_iff_exists_pos_dist_eq.mp h
  have h1 : dist b a = r * dist b' a' := by simpa using hd 1 0
  have h2 : dist b c = r * dist b' c' := by simpa using hd 1 2
  have ha : dist b' a' ≠ 0 := by
    intro h0; apply hba; rw [← dist_eq_zero, h1, h0, mul_zero]
  have hc : dist b' c' ≠ 0 := by
    intro h0; apply hbc; rw [← dist_eq_zero, h2, h0, mul_zero]
  rw [h1, h2]
  field_simp
""", *_GEO_FACT_IMPORTS,
    label="similar triangles have proportional sides (as ratios from the second vertex)")

# The textbook catalogue (chapters: angles, triangles, congruence, similarity, parallels,
# right triangles, midpoints, circles, quadrilaterals): ``geo.sss``, ``geo.thales``, …
from ._geometry_textbook import *  # noqa: E402, F403

LEMMAS = collect_lemmas(globals())

#: corresponding parts of congruent triangles (CPCTC): the six parts as one family. Cite
#: ``because=[geo.cpctc, "hcong"]``; Lean uses whichever part the step needs.
cpctc = (cpctc_ab, cpctc_bc, cpctc_ca, cpctc_angle_a, cpctc_angle_b,  # noqa: F405
         cpctc_angle_c)  # noqa: F405

__all__ = ["Point", "point", "points", "dist", "angle", "line", "parallel", "on_segment",
           "collinear", "triangle", "similar", "strictly_between", "extend_beyond",
           "perpendicular", "on_line",
           "segment_addition", "cross_multiply", "flip_ratio", "split_fraction",
           "congruent", "midpoint", "right_angle", "on_circle", "parallelogram",
           "is_midpoint", "opposite_sides", "same_side", "concyclic",
           "LEMMAS", "VERIFIED_MATHLIB", "cpctc",
           "CATALOG_VERSION", *LEMMAS]

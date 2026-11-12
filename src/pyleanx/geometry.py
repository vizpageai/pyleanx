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
dist_triangle = lemma("dist_triangle", _METRIC)
dist_nonneg = lemma("dist_nonneg", _METRIC)
dist_self = lemma("dist_self", _METRIC)
angle_comm = lemma("EuclideanGeometry.angle_comm", _ANGLE)
angle_nonneg = lemma("EuclideanGeometry.angle_nonneg", _ANGLE)
angle_le_pi = lemma("EuclideanGeometry.angle_le_pi", _ANGLE)
#: ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π, given p₂ ≠ p₁ (explicit argument p₃).
angle_add_angle_add_angle_eq_pi = lemma("EuclideanGeometry.angle_add_angle_add_angle_eq_pi",
                                        _TRIANGLE)
#: Pythagoras (both directions): |p₁p₃|² = |p₁p₂|² + |p₃p₂|²  ↔  ∠ p₁ p₂ p₃ = π / 2.
pythagoras_iff = lemma(
    "EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two", _RIGHT)

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


#: AA: two pairs of equal angles (at b and at c) make the triangles similar.
similar_AA = lemma("EuclideanGeometry.similar_of_angle_angle", _SIMILAR,
                   label="AA similarity")

_GEO_FACT_IMPORTS = (_SIMILAR, _ANGLE, _BETWEEN, _AFFINE, _COLLINEAR)
_corresponding_core = library_fact(
    "PyLeanX.Geometry.corresponding_angles_core", """
    theorem PyLeanX.Geometry.corresponding_angles_core {V P : Type*} [NormedAddCommGroup V]
        [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {A B C D E : P}
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
    """, *_GEO_FACT_IMPORTS, label="corresponding angles at parallel lines are equal")

#: D on AB, E on AC, DE ∥ BC  ⟹  ∠ABC = ∠ADE (corresponding angles).
corresponding_angles = library_fact(
    "PyLeanX.Geometry.corresponding_angles", """
    theorem PyLeanX.Geometry.corresponding_angles {V P : Type*} [NormedAddCommGroup V]
        [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {A B C D E : P}
        (hABC : ¬ Collinear ℝ {A, B, C}) (hD : Wbtw ℝ A D B) (hE : Wbtw ℝ A E C)
        (hP : (line[ℝ, D, E]).Parallel line[ℝ, B, C]) :
        EuclideanGeometry.angle A B C = EuclideanGeometry.angle A D E :=
      (PyLeanX.Geometry.corresponding_angles_core hABC hD hE hP).1
    """, *_GEO_FACT_IMPORTS, label="corresponding angles (DE ∥ BC)",
    requires=[_corresponding_core])

#: D on AB, E on AC, DE ∥ BC  ⟹  ∠BCA = ∠DEA (corresponding angles).
corresponding_angles_2 = library_fact(
    "PyLeanX.Geometry.corresponding_angles_2", """
    theorem PyLeanX.Geometry.corresponding_angles_2 {V P : Type*} [NormedAddCommGroup V]
        [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {A B C D E : P}
        (hABC : ¬ Collinear ℝ {A, B, C}) (hD : Wbtw ℝ A D B) (hE : Wbtw ℝ A E C)
        (hP : (line[ℝ, D, E]).Parallel line[ℝ, B, C]) :
        EuclideanGeometry.angle B C A = EuclideanGeometry.angle D E A :=
      (PyLeanX.Geometry.corresponding_angles_core hABC hD hE hP).2
    """, *_GEO_FACT_IMPORTS, label="corresponding angles (DE ∥ BC)",
    requires=[_corresponding_core])

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

LEMMAS = collect_lemmas(globals())

__all__ = ["Point", "point", "points", "dist", "angle", "line", "parallel", "on_segment",
           "collinear", "triangle", "similar", "LEMMAS", "VERIFIED_MATHLIB",
           "CATALOG_VERSION", *LEMMAS]

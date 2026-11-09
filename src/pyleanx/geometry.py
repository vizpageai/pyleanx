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
* Points support only ``=`` and ``≠``; no coordinates, vector arithmetic, lines,
  circles or oriented angles yet. The general AA-similarity theorem is out of scope.
* ``LEMMAS`` reference declarations at :data:`VERIFIED_MATHLIB`; Lean checks every use.
"""

from __future__ import annotations

from collections.abc import Iterable

from ._domain import CATALOG_VERSION, VERIFIED_MATHLIB, collect_lemmas, lemma
from ._origin import caller_origin
from .errors import ScopeError
from .expr import App, Func, Var, make_var
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

LEMMAS = collect_lemmas(globals())

__all__ = ["Point", "point", "points", "dist", "angle", "LEMMAS", "VERIFIED_MATHLIB",
           "CATALOG_VERSION", *LEMMAS]

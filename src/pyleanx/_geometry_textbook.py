"""High-school plane geometry, chapter by chapter: the facts a textbook proof cites.

Every name here is available as ``geo.<name>`` and is cited with ``because=``:

    pl.claim(geo.congruent((B, M, A), (C, M, A)), because=geo.sss)
    pl.claim(geo.angle(B, M, A) == geo.angle(C, M, A), because=geo.cpctc_angle_b)

Two kinds of facts:

* references to theorems in the pinned Mathlib (checked by name against it), and
* facts Mathlib does not state in textbook form, shipped as Lean theorems *with their
  proofs* (``PyLeanX.Geometry.*``): every Lean file that cites one contains its proof.

Conventions (as in Mathlib): ``∠ABC`` is the unoriented angle at B, in radians (π = 180°);
"M is the midpoint of AB" is the hypothesis ``M = midpoint ℝ A B`` (``geo.is_midpoint``);
"B and D are on opposite sides of line AC" is ``geo.opposite_sides(B, D, A, C)``.
Statements hold in every Euclidean space; plane-only facts are marked.
"""

from __future__ import annotations

from ._domain import lemma
from .proofs import library_fact

_AFF = "Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine"
_TRI = "Mathlib.Geometry.Euclidean.Triangle"
_RIGHT = "Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle"
_COLL = "Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional"
_CONG = "Mathlib.Geometry.Euclidean.Congruence"
_SIM = "Mathlib.Geometry.Euclidean.Similarity"
_SIM_DEF = "Mathlib.Topology.MetricSpace.Similarity"
_AFFSUB = "Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic"
_PERP = "Mathlib.Geometry.Euclidean.PerpBisector"
_POWER = "Mathlib.Geometry.Euclidean.Sphere.Power"
_SIDE = "Mathlib.Analysis.Convex.Side"
_METRIC = "Mathlib.Topology.MetricSpace.Pseudo.Defs"
_SHIP = (_CONG, _SIM, _TRI, _RIGHT, _AFF, _SIDE, _PERP, "Mathlib.Analysis.Normed.Affine.Convex",
         "Mathlib.Analysis.Normed.Affine.AddTorsor", "Mathlib.LinearAlgebra.AffineSpace.Midpoint")

# ---------------------------------------------------------------------------------------
# 1. Angles
# ---------------------------------------------------------------------------------------
angle_comm = lemma("EuclideanGeometry.angle_comm", _AFF, label="∠ABC = ∠CBA")
vertical_angles = lemma("EuclideanGeometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi", _AFF,
                        label="vertical angles are equal")
linear_pair = lemma("EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi", _AFF,
                    label="angles on a straight line add up to 180°")
straight_angle = lemma("Sbtw.angle₁₂₃_eq_pi", _AFF,
                       label="B strictly between A and C makes ∠ABC a straight angle")
angle_addition = lemma("EuclideanGeometry.angle_add_angle_eq_of_sbtw", _TRI,
                       label="angle addition")

# ---------------------------------------------------------------------------------------
# 2. Triangles
# ---------------------------------------------------------------------------------------
angle_sum = lemma("EuclideanGeometry.angle_add_angle_add_angle_eq_pi", _TRI,
                  label="the angles of a triangle add up to 180°")
exterior_angle = lemma("EuclideanGeometry.exterior_angle_eq_angle_add_angle", _TRI,
                       label="an exterior angle equals the sum of the remote interior angles")
isosceles_base_angles = lemma("EuclideanGeometry.angle_eq_angle_of_dist_eq", _TRI,
                              label="the base angles of an isosceles triangle are equal")
isosceles_converse = lemma("EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi", _TRI,
                           label="equal base angles make the triangle isosceles")
larger_side_larger_angle = lemma("EuclideanGeometry.angle_lt_iff_dist_lt", _TRI,
                                 label="the larger side is opposite the larger angle")
distinct_ab = lemma("ne₁₂_of_not_collinear", _COLL, label="the vertices of a triangle are distinct")
distinct_ac = lemma("ne₁₃_of_not_collinear", _COLL, label="the vertices of a triangle are distinct")
distinct_bc = lemma("ne₂₃_of_not_collinear", _COLL, label="the vertices of a triangle are distinct")

# ---------------------------------------------------------------------------------------
# 3. Congruent triangles (ABC ≅ A'B'C', vertices in corresponding order)
# ---------------------------------------------------------------------------------------
sss = lemma("EuclideanGeometry.side_side_side", _CONG, label="SSS")
sas = lemma("EuclideanGeometry.side_angle_side", _CONG, label="SAS")
asa = lemma("EuclideanGeometry.angle_side_angle", _CONG, label="ASA")
aas = lemma("EuclideanGeometry.angle_angle_side", _CONG, label="AAS")

# ---------------------------------------------------------------------------------------
# 4. Similar triangles
# ---------------------------------------------------------------------------------------
similar_SAS = lemma("EuclideanGeometry.similar_of_side_angle_side", _SIM, label="SAS similarity")
similar_SSS = lemma("similar_of_dist_mul_eq_dist_mul_eq", _SIM_DEF, label="SSS similarity")
similar_angles = lemma("Similar.angle_eq", _SIM,
                       label="corresponding angles of similar triangles are equal")

# ---------------------------------------------------------------------------------------
# 5. Parallel lines
# ---------------------------------------------------------------------------------------
parallel_trans = lemma("AffineSubspace.Parallel.trans", _AFFSUB,
                       label="lines parallel to the same line are parallel")
parallel_symm = lemma("AffineSubspace.Parallel.symm", _AFFSUB, label="parallelism is symmetric")

# ---------------------------------------------------------------------------------------
# 6. Right triangles and trigonometry
# ---------------------------------------------------------------------------------------
law_of_cosines = lemma("EuclideanGeometry.law_cos", _TRI, label="the law of cosines")
law_of_sines = lemma("EuclideanGeometry.law_sin", _TRI, label="the law of sines")

# ---------------------------------------------------------------------------------------
# 7. Midpoints and perpendicular bisectors
# ---------------------------------------------------------------------------------------
median_to_base_is_perpendicular = lemma(
    "EuclideanGeometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq", _AFF,
    label="the median to the base of an isosceles triangle is perpendicular to it")
perpendicular_bisector = lemma("AffineSubspace.mem_perpBisector_iff_dist_eq", _PERP,
                               label="points on the perpendicular bisector are equidistant")

# ---------------------------------------------------------------------------------------
# 8. Circles
# ---------------------------------------------------------------------------------------
intersecting_chords = lemma("EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi",
                            _POWER, label="intersecting chords: PA·PB = PC·PD")

# ---------------------------------------------------------------------------------------
# Shipped facts (Lean theorems with proofs; Mathlib does not state them in this form)
# ---------------------------------------------------------------------------------------

cpctc_ab = library_fact("PyLeanX.Geometry.cpctc_ab", """
theorem PyLeanX.Geometry.cpctc_ab {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {a b c a' b' c' : P}
    (h : Congruent ![a, b, c] ![a', b', c']) : dist a b = dist a' b' := by
  simpa using h.dist_eq 0 1
""", *_SHIP,
    label="corresponding parts of congruent triangles (CPCTC)")

cpctc_bc = library_fact("PyLeanX.Geometry.cpctc_bc", """
theorem PyLeanX.Geometry.cpctc_bc {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {a b c a' b' c' : P}
    (h : Congruent ![a, b, c] ![a', b', c']) : dist b c = dist b' c' := by
  simpa using h.dist_eq 1 2
""", *_SHIP,
    label="corresponding parts of congruent triangles (CPCTC)")

cpctc_ca = library_fact("PyLeanX.Geometry.cpctc_ca", """
theorem PyLeanX.Geometry.cpctc_ca {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {a b c a' b' c' : P}
    (h : Congruent ![a, b, c] ![a', b', c']) : dist c a = dist c' a' := by
  simpa using h.dist_eq 2 0
""", *_SHIP,
    label="corresponding parts of congruent triangles (CPCTC)")

cpctc_angle_a = library_fact("PyLeanX.Geometry.cpctc_angle_a", """
theorem PyLeanX.Geometry.cpctc_angle_a {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {a b c a' b' c' : P}
    (h : Congruent ![a, b, c] ![a', b', c']) :
    EuclideanGeometry.angle c a b = EuclideanGeometry.angle c' a' b' := by
  simpa using EuclideanGeometry.angle_eq_of_congruent h 2 0 1
""", *_SHIP,
    label="corresponding parts of congruent triangles (CPCTC)")

cpctc_angle_b = library_fact("PyLeanX.Geometry.cpctc_angle_b", """
theorem PyLeanX.Geometry.cpctc_angle_b {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {a b c a' b' c' : P}
    (h : Congruent ![a, b, c] ![a', b', c']) :
    EuclideanGeometry.angle a b c = EuclideanGeometry.angle a' b' c' := by
  simpa using EuclideanGeometry.angle_eq_of_congruent h 0 1 2
""", *_SHIP,
    label="corresponding parts of congruent triangles (CPCTC)")

cpctc_angle_c = library_fact("PyLeanX.Geometry.cpctc_angle_c", """
theorem PyLeanX.Geometry.cpctc_angle_c {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {a b c a' b' c' : P}
    (h : Congruent ![a, b, c] ![a', b', c']) :
    EuclideanGeometry.angle b c a = EuclideanGeometry.angle b' c' a' := by
  simpa using EuclideanGeometry.angle_eq_of_congruent h 1 2 0
""", *_SHIP,
    label="corresponding parts of congruent triangles (CPCTC)")

hl = library_fact("PyLeanX.Geometry.hypotenuse_leg", """
theorem PyLeanX.Geometry.hypotenuse_leg {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {a b c a' b' c' : P}
    (h : EuclideanGeometry.angle a b c = Real.pi / 2)
    (h' : EuclideanGeometry.angle a' b' c' = Real.pi / 2)
    (hac : dist a c = dist a' c') (hab : dist a b = dist a' b') :
    Congruent ![a, b, c] ![a', b', c'] := by
  have p := (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two a b c).2 h
  have p' :=
    (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two a' b' c').2 h'
  have hcb : dist c b = dist c' b' := by
    have hsq : dist c b * dist c b = dist c' b' * dist c' b' := by
      rw [hac, hab] at p; linarith
    nlinarith [dist_nonneg (x := c) (y := b), dist_nonneg (x := c') (y := b')]
  refine EuclideanGeometry.side_side_side hab ?_ ?_
  · rw [dist_comm, hcb, dist_comm]
  · rw [dist_comm, hac, dist_comm]
""", *_SHIP,
    label="HL (hypotenuse–leg)")

parallel_direction = library_fact("PyLeanX.Geometry.parallel_vsub", """
theorem PyLeanX.Geometry.parallel_vsub {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {A B C D : P}
    (hP : (line[ℝ, A, B]).Parallel line[ℝ, C, D]) : ∃ k : ℝ, D -ᵥ C = k • (B -ᵥ A) := by
  have hd := hP.direction_eq
  rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair, vectorSpan_pair] at hd
  have hmem : D -ᵥ C ∈ ℝ ∙ (C -ᵥ D) := by
    rw [Submodule.mem_span_singleton]
    exact ⟨-1, by rw [neg_one_smul, neg_vsub_eq_vsub_rev]⟩
  rw [← hd, Submodule.mem_span_singleton] at hmem
  obtain ⟨k, hk⟩ := hmem
  exact ⟨-k, by rw [← hk, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]⟩
""", *_SHIP,
    label="parallel lines have the same direction")

alternate_angles = library_fact("PyLeanX.Geometry.alternate_angles", """
theorem PyLeanX.Geometry.alternate_angles {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {A B C D : P}
    (hP : (line[ℝ, A, B]).Parallel line[ℝ, C, D]) (hs : (line[ℝ, A, C]).SOppSide B D) :
    EuclideanGeometry.angle B A C = EuclideanGeometry.angle A C D := by
  obtain ⟨k, hk⟩ := PyLeanX.Geometry.parallel_vsub hP
  have hkneg : k < 0 := by
    by_contra hk0
    push Not at hk0
    have hD : D = k • (B -ᵥ A) +ᵥ C := by rw [← hk, vsub_vadd]
    have hw : (line[ℝ, A, C]).WSameSide D B := by
      rw [hD]
      exact AffineSubspace.wSameSide_smul_vsub_vadd_left B (left_mem_affineSpan_pair _ _ _)
        (right_mem_affineSpan_pair _ _ _) hk0
    exact hw.symm.not_sOppSide hs
  simp only [EuclideanGeometry.angle]
  rw [hk, ← neg_vsub_eq_vsub_rev C A,
    show k • (B -ᵥ A) = -((-k) • (B -ᵥ A)) by rw [neg_smul, neg_neg],
    InnerProductGeometry.angle_neg_neg,
    InnerProductGeometry.angle_smul_right_of_pos _ _ (by linarith),
    InnerProductGeometry.angle_comm]
""", *_SHIP,
    label="alternate interior angles are equal",
    requires=[parallel_direction])

cointerior_angles = library_fact("PyLeanX.Geometry.cointerior_angles", """
theorem PyLeanX.Geometry.cointerior_angles {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {A B C D : P}
    (hP : (line[ℝ, A, B]).Parallel line[ℝ, C, D]) (hs : (line[ℝ, A, C]).SSameSide B D) :
    EuclideanGeometry.angle B A C + EuclideanGeometry.angle A C D = Real.pi := by
  obtain ⟨k, hk⟩ := PyLeanX.Geometry.parallel_vsub hP
  have hkpos : 0 < k := by
    by_contra hk0
    push Not at hk0
    have hD : D = k • (B -ᵥ A) +ᵥ C := by rw [← hk, vsub_vadd]
    have hw : (line[ℝ, A, C]).WOppSide D B := by
      rw [hD]
      exact AffineSubspace.wOppSide_smul_vsub_vadd_left B (left_mem_affineSpan_pair _ _ _)
        (right_mem_affineSpan_pair _ _ _) hk0
    exact hs.symm.not_wOppSide hw
  simp only [EuclideanGeometry.angle]
  rw [hk, ← neg_vsub_eq_vsub_rev C A, InnerProductGeometry.angle_neg_left,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hkpos, InnerProductGeometry.angle_comm]
  ring
""", *_SHIP,
    label="co-interior angles add up to 180°",
    requires=[parallel_direction])

midpoint_equal_halves = library_fact("PyLeanX.Geometry.midpoint_equal_halves", """
theorem PyLeanX.Geometry.midpoint_equal_halves {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {a b m : P}
    (h : m = midpoint ℝ a b) : dist a m = dist b m := by
  subst h; exact dist_left_midpoint_eq_dist_right_midpoint a b
""", *_SHIP,
    label="the midpoint divides a segment into equal halves")

midpoint_half = library_fact("PyLeanX.Geometry.midpoint_half", """
theorem PyLeanX.Geometry.midpoint_half {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {a b m : P}
    (h : m = midpoint ℝ a b) : dist a m = dist a b / 2 := by
  subst h; rw [dist_left_midpoint, Real.norm_two]; ring
""", *_SHIP,
    label="each half is half the segment")

midpoint_straight = library_fact("PyLeanX.Geometry.midpoint_straight", """
theorem PyLeanX.Geometry.midpoint_straight {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {a b m : P}
    (h : m = midpoint ℝ a b) (hab : a ≠ b) : EuclideanGeometry.angle a m b = Real.pi := by
  subst h; exact EuclideanGeometry.angle_midpoint_eq_pi a b hab
""", *_SHIP,
    label="a midpoint lies on the segment, so the angle there is a straight angle")

midsegment_parallel = library_fact("PyLeanX.Geometry.midsegment_parallel", """
theorem PyLeanX.Geometry.midsegment_parallel {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {a b c m n : P}
    (hm : m = midpoint ℝ a b) (hn : n = midpoint ℝ a c) :
    (line[ℝ, m, n]).Parallel line[ℝ, b, c] := by
  subst hm hn
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq, vectorSpan_pair, vectorSpan_pair]
  have h : midpoint ℝ a b -ᵥ midpoint ℝ a c = (2 : ℝ)⁻¹ • (b -ᵥ c) := by
    rw [midpoint_vsub_midpoint, vsub_self, midpoint_eq_smul_add, zero_add, invOf_eq_inv]
  rw [h, Submodule.span_singleton_smul_eq (IsUnit.inv (Ne.isUnit two_ne_zero))]
""", *_SHIP,
    label="midsegment theorem: the segment joining two midpoints is parallel to the third side")

midsegment_length = library_fact("PyLeanX.Geometry.midsegment_length", """
theorem PyLeanX.Geometry.midsegment_length {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {a b c m n : P}
    (hm : m = midpoint ℝ a b) (hn : n = midpoint ℝ a c) : dist m n = dist b c / 2 := by
  subst hm hn
  rw [dist_eq_norm_vsub V, midpoint_vsub_midpoint, vsub_self, midpoint_eq_smul_add, zero_add,
    invOf_eq_inv, norm_smul, dist_eq_norm_vsub V, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  ring
""", *_SHIP,
    label="midsegment theorem: the segment joining two midpoints is half the third side")

thales = library_fact("PyLeanX.Geometry.thales", """
theorem PyLeanX.Geometry.thales {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {A B O Q : P}
    (hO : O = midpoint ℝ A B) (hQ : dist Q O = dist A O) :
    EuclideanGeometry.angle A Q B = Real.pi / 2 := by
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  have hBO : B -ᵥ O = -(A -ᵥ O) := by
    rw [hO, left_vsub_midpoint, right_vsub_midpoint, ← smul_neg, neg_vsub_eq_vsub_rev]
  have hA : A -ᵥ Q = (A -ᵥ O) - (Q -ᵥ O) := (vsub_sub_vsub_cancel_right A Q O).symm
  have hB : B -ᵥ Q = (B -ᵥ O) - (Q -ᵥ O) := (vsub_sub_vsub_cancel_right B Q O).symm
  rw [hA, hB, hBO]
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V] at hQ
  simp only [inner_sub_left, inner_sub_right, inner_neg_right, inner_neg_left,
    real_inner_self_eq_norm_sq, real_inner_comm (A -ᵥ O) (Q -ᵥ O)]
  rw [hQ]; ring
""", *_SHIP,
    label="Thales: an angle inscribed in a semicircle is a right angle")

parallelogram_diagonal_sides = library_fact("PyLeanX.Geometry.parallelogram_opposite_sides", """
theorem PyLeanX.Geometry.parallelogram_opposite_sides {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {A B C D : P}
    (h : ¬ Collinear ℝ {A, B, C} ∧ (line[ℝ, A, B]).Parallel line[ℝ, C, D] ∧
      (line[ℝ, C, B]).Parallel line[ℝ, A, D]) :
    (line[ℝ, A, C]).SOppSide B D ∧ (line[ℝ, C, A]).SOppSide B D := by
  obtain ⟨hT, h1, h2⟩ := h
  obtain ⟨k, hk⟩ := PyLeanX.Geometry.parallel_vsub h1   -- D -ᵥ C = k • (B -ᵥ A)
  obtain ⟨m, hm⟩ := PyLeanX.Geometry.parallel_vsub h2   -- D -ᵥ A = m • (B -ᵥ C)
  -- B -ᵥ A and B -ᵥ C are independent (ABC is a triangle), so k = -1
  have key : (k + 1) • (B -ᵥ A) = (m + 1) • (B -ᵥ C) := by
    have e : D -ᵥ A = (D -ᵥ C) + (C -ᵥ B) + (B -ᵥ A) := by
      rw [vsub_add_vsub_cancel, vsub_add_vsub_cancel]
    rw [hm, hk, ← neg_vsub_eq_vsub_rev B C] at e
    linear_combination (norm := module) e.symm
  have hk1 : k = -1 := by
    by_contra hne
    have hk0 : k + 1 ≠ 0 := fun h0 => hne (by linarith)
    apply hT
    rw [collinear_iff_of_mem (p₀ := B) (by simp)]
    refine ⟨B -ᵥ C, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro p (rfl | rfl | rfl)
    · refine ⟨-((k + 1)⁻¹ * (m + 1)), ?_⟩
      have : p -ᵥ B = -((k + 1)⁻¹ * (m + 1)) • (B -ᵥ C) := by
        rw [← neg_vsub_eq_vsub_rev, neg_smul, mul_smul, ← key, smul_smul,
          inv_mul_cancel₀ hk0, one_smul]
      rw [← this, vsub_vadd]
    · exact ⟨0, by simp⟩
    · exact ⟨-1, by rw [neg_one_smul, neg_vsub_eq_vsub_rev, vsub_vadd]⟩
  have hD : D = (-1 : ℝ) • (B -ᵥ A) +ᵥ C := by rw [← hk1, ← hk, vsub_vadd]
  have hB : B ∉ line[ℝ, A, C] := fun hm' => hT (by
    have := collinear_insert_of_mem_affineSpan_pair hm'
    rwa [Set.insert_comm] at this)
  have h1' : (line[ℝ, A, C]).SOppSide B D := by
    rw [hD]
    exact (AffineSubspace.sOppSide_smul_vsub_vadd_left hB (left_mem_affineSpan_pair _ _ _)
      (right_mem_affineSpan_pair _ _ _) (by norm_num)).symm
  exact ⟨h1', by rwa [Set.pair_comm]⟩
""", *_SHIP,
    label="a diagonal of a parallelogram separates the other two vertices",
    requires=[parallel_direction])


# Small facts used to restate a step in another order
midpoint_comm = lemma("midpoint_comm", "Mathlib.LinearAlgebra.AffineSpace.Midpoint",
                      label="the midpoint of AB is the midpoint of BA")
dist_comm = lemma("dist_comm", _METRIC, label="AB = BA")

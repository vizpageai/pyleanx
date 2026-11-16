# Writing proofs the way mathematicians do

A proof in a textbook is a list of statements, each with a reason: *"Let ε > 0. Choose N₁
with |aₙ − A| < ε/2 for n ≥ N₁ … Hence |aₙ + bₙ − (A + B)| < ε."* PyLeanX lets you write
exactly that, in any area of mathematics, and Lean checks every step.

```python
import pyleanx as pl
from pyleanx import numbers as nt

n, p, N = pl.symbols("n p N", pl.Nat)

infinitely_many_primes = pl.Theorem(
    "infinitely_many_primes", [n],
    conclusion=pl.Exists(p, pl.And(n < p, nt.prime(p))),
    proof=pl.proof(
        pl.let(N, nt.factorial(n) + 1),
        pl.claim(nt.factorial(n) > 0, because=nt.factorial_pos),
        pl.claim(N != 1, note="n! > 0, so N ≥ 2"),
        pl.choose(p, such_that=pl.And(nt.prime(p), nt.divides(p, N)),
                  because=nt.exists_prime_dvd, names="hp hpN"),
        pl.take(p),
        pl.claim(n < p, proof=pl.proof(
            pl.suppose_not(p <= n, name="hle"),
            pl.claim(nt.divides(p, nt.factorial(n)), because=[nt.dvd_factorial, nt.prime_pos]),
            pl.claim(nt.divides(p, 1), because=nt.dvd_add_right, note="p ∣ n! and p ∣ n! + 1"),
            pl.conclude(because=nt.prime_not_dvd_one),
        )),
        pl.conclude(),
    ),
)
result = infinitely_many_primes.verify()
print(infinitely_many_primes.prose(result))
```

```text
Theorem (infinitely_many_primes). For all n ∈ ℕ: ∃ p ∈ ℕ, n < p ∧ p is prime.
Proof.
  1. Let N = n! + 1.
  2. n! > 0.  (n! > 0)
  3. N ≠ 1.  (n! > 0, so N ≥ 2)
  4. Choose p such that p is prime ∧ p ∣ N.  (every n ≠ 1 has a prime factor)
  5. Take p.
  6. n < p.
    Proof.
    6.1. Suppose, for contradiction, that p ≤ n.
    6.2. p ∣ n!.  (m ∣ n! for 0 < m ≤ n, a prime is positive)
    6.3. p ∣ 1.  (p ∣ n! and p ∣ n! + 1)
    This is a contradiction (a prime does not divide 1).
  Hence n < p ∧ p is prime. ∎
  ✔ Checked by Lean (axioms: propext, Classical.choice, Quot.sound).
```

## The moves of a proof

| Python | In words | Lean |
|---|---|---|
| `pl.claim(P, because=…, note=…)` | *P holds, because …* | `have stepN : P := by …` |
| `pl.conclude(because=…)` | *Hence the goal* / *a contradiction* | closes the goal |
| `pl.let(f, value)` | *Let f = …* (`value` may be a `lambda`) | `set f := … with f_def` |
| `pl.fix(x, assume={"h": P})` | *Let x be arbitrary with P* (e.g. *let ε > 0*) | `intro x (h : P)` |
| `pl.assume(P, name="h")` | *Assume P* (goal P ⇒ Q) | `intro (h : P)` |
| `pl.take(w)` | *Take x = w* (goal ∃ x, …) | `refine ⟨w, ?_⟩` |
| `pl.take(w, such_that=P, because=…)` | *Take δ = ε/3 > 0* (goal ∃ x, P x ∧ Q x) | `refine ⟨w, ?_, ?_⟩`, P proved in a bullet |
| `pl.choose(x, such_that=P, because=…, names="h")` | *Choose x with P(x)* | `obtain ⟨x, h⟩ : ∃ x, P := by …` |
| `pl.suppose_not(P, name="h")` | *Suppose, for contradiction, that P* | `by_contra`, then `have h : P` |
| `pl.cases_on(pl.case(P₁, steps…), pl.case(P₂, …), because=…)` | *Either P₁ or P₂.* Case 1 … Case 2 … | `rcases (P₁ ∨ P₂) with h \| h` |
| `pl.induction_on(n, base=[…], step=[…], k=k, ih="ih")` | *Induction on n: base case, inductive step* | `induction n with \| zero \| succ k ih` |
| `pl.chain(a, ("=", b, because), ("<=", c, because, note), …)` | *a = b ≤ c* with a reason per link | `calc` |
| `pl.suffices(P, because=…)` | *It suffices to show P* | `suffices h : P by …` |

* **`because`** is a fact or a list of facts: library facts (`nt.even_or_odd`,
  `an.tendsto_iff`, `geo.similar_AA`, anything in `pl.mathlib`), hypotheses (`"h"`), or
  named earlier steps. Everything proved so far is available without being cited.
* **`note`** is the reason in words, shown when the proof is printed. Lean ignores it.
* Steps are named `step1`, `step2`, … by position (`step6_2` inside step 6); pass
  `name="h"` to cite one by name. Printed proofs use the same numbers.
* A block that ends with `pl.chain(...)` concludes with it.
* `pl.case`, `base=` and `step=` take the steps of that part of the proof; a claim can have
  its own sub-proof with `proof=pl.proof(...)`.

## How each step is checked

The gap between the cited facts and the step is filled by standard automation. It tries
each of these in turn, and an attempt counts only if it closes the step completely:

* use a cited fact directly, apply it and discharge its side conditions from what is
  known, apply it to another cited fact (`L h`), rewrite with it, or use the half of it the
  step needs (one side of an `∧`, one direction of an `↔`);
* `simp`/`norm_num` with the facts, `linarith`/`nlinarith`, `omega`, `ring`, `field_simp`,
  `push_cast`, `fun_prop`, `positivity`, and splitting `∧`;
* the same after unfolding `pl.let` definitions and introducing `∀` variables.

Nothing is assumed. If no attempt works, Lean reports an error at that step and the proof
is not verified. Then split the step into smaller ones, cite the missing fact, or give
`proof=` an explicit tactic. In the example, "N ≠ 1 because n! > 0" is two steps, because
the automation cannot instantiate `n! > 0` by itself.

## Examples by area

| Area | Example | Moves used |
|---|---|---|
| Number theory | `readable_infinite_primes.py` (Euclid) | let, choose, take, contradiction, sub-proof |
| Number theory | `readable_consecutive_even.py` (n(n+1) is even) | cases, choose, take |
| Analysis | `readable_limit_sum.py` (limit of a sum, ε–N) | suffices, fix, choose, take, chain |
| Analysis | `readable_trig.py` (sin²+cos²=1 by derivatives) | let, claims, `avoid=` |
| Algebra | `readable_group_abelian.py` (x² = 1 for all x ⇒ abelian) | abstract group, chain |
| Inequalities | `readable_bernoulli.py` ((1+x)ⁿ ≥ 1+nx) | induction, chain |
| Inequalities | `readable_am_gm.py` (AM–GM) | claims with library facts |
| Geometry | `readable_side_splitter.py` (side-splitter) | similar triangles, shipped facts |
| Geometry | `readable_angle_bisector.py` (angle bisector theorem) | auxiliary point, cites the side-splitter theorem |
| Geometry | `textbook_geometry.py` (isosceles median, parallelogram sides, semicircle, isosceles right triangle, medial triangle) | congruence, CPCTC, parallels, Thales, midsegments |
| Real analysis | `analysis_lecture.py` (1/(n+1) → 0, uniqueness of limits, ε–δ continuity, bounded ⇒ Cauchy subsequence, shifted limits, sign of a limit, IVT root, convergent ⇒ Cauchy) | suffices, fix, choose, take with a side condition, contradiction, chain, big theorems |
| Harmonic analysis | `harmonic_lecture.py` (smoothness ⇒ decay of Fourier coefficients, Riemann–Lebesgue from Bessel, uniqueness from inversion, 1/n² decay, vanishing coefficients, f(0) = ∫ f̂) | citing Parseval/Bessel/inversion, citing a proved example, chain |
| Complex analysis | `readable_cauchy_integral.py` (Cauchy's integral formula from Cauchy's theorem) | let, chain, shipped facts, `avoid=` |

## Auxiliary constructions

A construction is a `pl.let` that names a new point; later steps prove its properties and
use it. The angle bisector theorem (`readable_angle_bisector.py`) extends BA beyond A to E
with AE = AC and applies the side-splitter theorem to triangle BEC:

```python
from readable_side_splitter import side_splitter      # proved earlier

pl.let(E, geo.extend_beyond(B, A, dist(A, C)), note="extend BA beyond A to E with AE = AC"),
pl.claim(geo.on_segment(A, B, E), because=geo.extension_between),
pl.claim(dist(A, E) == dist(A, C), because=geo.extension_length),
pl.claim(geo.parallel(geo.line(A, D), geo.line(E, C)), because=geo.bisector_parallel),
pl.claim(geo.triangle(B, E, C), because=geo.extension_triangle),
...
pl.claim(dist(B, A) / dist(B, E) == dist(B, D) / dist(B, C), because=side_splitter),
```

```text
1. Let E = the point on ray BA beyond A.  (extend BA beyond A to E with AE = AC)
...
4. AD ∥ EC.  (△ACE is isosceles (AE = AC), so EC is parallel to the bisector AD)
...
7. |BA|/|BE| = |BD|/|BC|.  (theorem side_splitter_similar)
...
Hence |BD|/|DC| = |AB|/|AC|. ∎
✔ Checked by Lean (axioms: propext, Classical.choice, Quot.sound).
```

The construction facts (`geo.extension_*`, `geo.bisector_parallel`) are shipped with their
Lean proofs. The parallel step is proved with vectors (equal angles give
(1 − s)|AB| = s|AC| for D = B + s(C − B), and then E − C is a multiple of A − D), not by
the angle chase in the note. Euclid (Elements VI.3) draws the parallel first and deduces
AE = AC; this proof fixes AE = AC and deduces the parallel. Both use the same triangle.

## High-school plane geometry

`pyleanx.geometry` (`geo`) has the vocabulary and the facts of a high-school course, so
textbook proofs can be written step by step (`examples/textbook_geometry.py`):

```python
isosceles_median = pl.Theorem(
    "isosceles_median_perpendicular", [A, B, C, M],
    assumptions={"hABC": geo.triangle(A, B, C), "hiso": dist(A, B) == dist(A, C),
                 "hM": geo.is_midpoint(M, B, C)},
    conclusion=geo.right_angle(A, M, B),
    proof=pl.proof(
        pl.claim(dist(B, M) == dist(C, M), because=geo.midpoint_equal_halves),
        pl.claim(geo.congruent((B, M, A), (C, M, A)), because=geo.sss),
        pl.claim(angle(B, M, A) == angle(C, M, A), because=geo.cpctc_angle_b),
        pl.claim(B != C, because=geo.distinct_bc("hABC")),
        pl.claim(angle(B, M, C) == pi(), because=geo.midpoint_straight),
        pl.claim(angle(A, M, B) + angle(A, M, C) == pi(), because=geo.linear_pair),
        pl.conclude(because=geo.angle_comm),
    ),
)
```

```text
1. |BM| = |CM|.  (the midpoint divides a segment into equal halves)
2. △BMA ≅ △CMA.  (SSS: BM = CM, MA = MA, AB = AC)
3. ∠BMA = ∠CMA.  (corresponding parts of congruent triangles (CPCTC))
...
Hence ∠AMB = π/2 (two equal angles adding up to 180°). ∎
✔ Checked by Lean (axioms: propext, Classical.choice, Quot.sound).
```

**Vocabulary:** `points`, `dist`, `angle`, `line`, `parallel`, `on_segment`,
`strictly_between`, `collinear`, `triangle`, `right_angle`, `congruent`, `similar`,
`midpoint`, `is_midpoint`, `opposite_sides`, `same_side`, `on_circle`, `concyclic`,
`parallelogram`, `extend_beyond`.

**Facts, by chapter** (cite with `because=`; each prints as the textbook reason):

| Chapter | Facts |
|---|---|
| Angles | `angle_comm`, `vertical_angles`, `linear_pair`, `straight_angle`, `angle_addition` |
| Triangles | `angle_sum`, `exterior_angle`, `isosceles_base_angles`, `isosceles_converse`, `larger_side_larger_angle`, `distinct_ab/ac/bc`, `triangle_sides_pos` |
| Congruence | `sss`, `sas`, `asa`, `aas`, `hl`, CPCTC: `cpctc_ab/bc/ca`, `cpctc_angle_a/b/c` |
| Similarity | `similar_AA`, `similar_SAS`, `similar_SSS`, `similar_angles`, `similar_sides` |
| Parallel lines | `alternate_angles`, `cointerior_angles`, `corresponding_angles`, `parallel_trans`, `parallel_symm` |
| Right triangles | `pythagoras_iff`, `law_of_cosines`, `law_of_sines`, `dist_triangle` |
| Midpoints | `midpoint_equal_halves`, `midpoint_half`, `midpoint_straight`, `midsegment_parallel`, `midsegment_length`, `median_to_base_is_perpendicular`, `perpendicular_bisector` |
| Circles | `thales`, `intersecting_chords` |
| Quadrilaterals | `parallelogram_diagonal_sides` |
| Constructions | `extension_between/length/triangle`, `bisector_parallel`, `componendo` |

Facts Mathlib states in textbook form are references to it; the others (CPCTC, HL, parallel
line angles, midpoints, midsegments, Thales, parallelograms, constructions) are shipped as
Lean theorems with their proofs and re-checked in every file that cites them.

Conventions: angles are unoriented and in radians (`pl.analysis.pi()` is 180°); "M is the
midpoint of AB" is the hypothesis `geo.is_midpoint(M, A, B)`; where a textbook reads a fact
off the figure ("B and D are on opposite sides of AC"), the proof states it as a step
(`geo.opposite_sides`) and justifies it. Steps that only reorder ("∠BAC = ∠CAB", "△BAC is
△ABC", "the midpoint of AB is the midpoint of BA") cite `geo.angle_comm`, `geo.dist_comm` or
`geo.midpoint_comm`, or the hypothesis being reordered.

Not covered yet: areas; the inscribed angle theorem and cyclic quadrilaterals (Mathlib has
them for oriented angles or the plane only); converses of the parallel-line angle facts;
tangent lines; "draw the line through P parallel to l" as a construction.

**Classroom notebook.** `examples/lecture_congruent_triangles.ipynb` is an interactive lecture
(SSS, SAS, ASA, CPCTC): slider figures to explore, two worked examples, a wrong proof that
Lean rejects at the faulty step, and four exercises students solve in the notebook with
`check(...)`. Its helpers and Lean-verified reference solutions are in
`examples/geometry_lecture.py` (`python examples/geometry_lecture.py` re-checks them).

## Real analysis as in a textbook

`pyleanx.analysis` (`an`) has the definitions of a first analysis course with their ε–N and
ε–δ unfoldings, and the big theorems under their textbook names, so a proof reads like the
book (`examples/lecture_real_analysis.ipynb`, solutions in `examples/analysis_lecture.py`):

```python
pl.Theorem("three_x_plus_one_continuous", [f, x0],
    assumptions={"hf": pl.Forall(t, f(t) == 3 * t + 1)},
    conclusion=an.continuous_at(f, x0),
    proof=pl.proof(
        pl.suffices(eps_delta(f, x0), because=an.continuous_at_iff),
        pl.fix(eps, assume={"hε": eps > 0}),
        pl.take(eps / 3, such_that=eps / 3 > 0),
        pl.fix(x, assume={"hx": pl.abs(x - x0) < eps / 3}),
        pl.chain(pl.abs(f(x) - f(x0)),
                 ("=", pl.abs(3 * (x - x0)), "hf", "f(x) = 3x + 1"),
                 ("=", 3 * pl.abs(x - x0), [an.abs_mul, an.abs_of_pos]),
                 ("<", 3 * (eps / 3)),
                 ("=", eps))))
```

```text
1. It suffices to show ∀ ε ∈ ℝ, ε > 0 → (∃ δ ∈ ℝ, δ > 0 ∧ (∀ x ∈ ℝ, |x - x₀| < δ → |f(x) - f(x₀)| < ε)).  (definition of continuity (ε–δ))
2. Let ε ∈ ℝ with ε > 0.
3. Take δ = ε/3; then ε/3 > 0.
4. Let x ∈ ℝ with |x - x₀| < ε/3.
5. |f(x) - f(x₀)| = |3(x - x₀)| (f(x) = 3x + 1) = 3 |x - x₀| (…) < 3 · ε/3 = ε.
```

**Definitions:** `tendsto` (unfold: `tendsto_iff`), `cauchy` (`cauchy_iff`), `continuous_at`
(`continuous_at_iff`), `uniformly_continuous_on` (`uniformly_continuous_iff`), `continuous`,
`continuous_on(f, a, b)` on [a, b], `differentiable_on(f, a, b)` on (a, b), `deriv`,
`increasing`, `strictly_increasing`, `bounded` (written out: ∃ M, ∀ n, |aₙ| ≤ M). A sequence given
by a formula, `pl.fun(lambda n: 1 / (n + 1), pl.Nat)`, prints as the formula: "1/(n + 1) → 0".

**Theorems** (29 shipped with Lean proofs, plus Mathlib references):

| Chapter | Facts |
|---|---|
| Limits | `limit_unique`, `limit_add`, `limit_sub`, `limit_mul`, `limit_const_mul`, `limit_const`, `squeeze`, `one_over_n`, `archimedean`, `reciprocal_lt` |
| Completeness | `convergent_bounded`, `convergent_cauchy`, `cauchy_convergent`, `monotone_convergence`, `increasing_of_step`, `bolzano_weierstrass` |
| Continuity | `sequential_continuity`, `ivt`, `evt_max`, `evt_min`, `heine_cantor`, `continuous_on_of_continuous`, `continuous_at_of_continuous` |
| Differentiation | `rolle`, `mvt`, `differentiable_on_of_differentiable`, `constant_of_zero_derivative`, `deriv_sin`, `deriv_cos` |
| Absolute value | `triangle_inequality`, `reverse_triangle`, `abs_sub_comm`, `abs_mul`, `abs_lt`, `abs_le`, `abs_pos`, `abs_of_pos`, `abs_of_nonneg`, `abs_nonneg`, `le_max_left`, `le_max_right` |

Written proofs print a cast `(n : ℝ)` as `n`, as a book does (Lean keeps the cast). Not covered
yet: series, Riemann integrals, sequences of functions, lim sup / lim inf, general metric
spaces.

## Harmonic analysis: Fourier series and the Fourier transform

`pyleanx.harmonic` (`ha`) follows the conventions of Stein–Shakarchi, *Fourier Analysis*:
f̂(n) = (1/2π) ∫_{−π}^{π} f(x) e^{−inx} dx (`ha.coeff`, Mathlib's `fourierCoeffOn` on [−π, π]) and
f̂(ξ) = ∫ f(x) e^{−2πixξ} dx (`ha.ft`, Mathlib's `𝓕`), with `ha.ift` the inverse transform
(`examples/lecture_harmonic_analysis.ipynb`, solutions in `examples/harmonic_lecture.py`):

```text
Theorem (fourier_uniqueness). For all f, g ∈ ℝ → ℂ: if f is continuous, g is continuous,
f ∈ L¹(ℝ), g ∈ L¹(ℝ), f̂ ∈ L¹(ℝ), ĝ ∈ L¹(ℝ), f̂ = ĝ, then ∀ x ∈ ℝ, f(x) = g(x).
Proof.
  1. Let x ∈ ℝ be arbitrary.
  2. g(x) = (ĝ)^(∨)(x).  (Fourier inversion formula)
  3. f(x) = (f̂)^(∨)(x) (Fourier inversion for f) = (ĝ)^(∨)(x) (f̂ = ĝ) = g(x) (Fourier inversion for g).
  Hence f(x) = g(x). ∎
```

**Vocabulary:** `coeff`, `coeff_seq`, `ft`, `ft_fun`, `ift`, `gauss`, `L2`, `integrable_on_circle`,
`integrable`, `continuous`, `coeff_sq_sum`, `mean_square`, `derivative(f, g)` (f′ = g),
`summable`, `tends_to_zero` (as |n| → ∞), `coeffs_tend_to_zero`.

**Facts:** `coeff_eq_integral`, `ft_eq_integral` (the definitions are the book's formulas),
`coeff_const_mul`, `coeff_add`, `coeff_derivative` ((f′)^(n) = in f̂(n)), `bessel_summable`,
`parseval`, `riemann_lebesgue_coeff`, `riemann_lebesgue`, `gaussian`, `inversion`, `ift_at_zero`,
and small steps (`terms_tend_to_zero`, `tendsto_zero_of_norm_sq`, `norm_I_mul_int`,
`abs_int_ne_zero`, `div_of_mul`, `div_div`, `sum_of_zero_coeffs`). The objects (f̂(n), L², the two
sides of Parseval, …) are small Lean definitions shipped with the facts; a shipped definition used
in a statement is emitted into the Lean file like a cited fact.

Not available, because Mathlib lacks them at the pinned version: Fejér/Dirichlet kernels and
summability, the Hardy–Littlewood maximal inequality, Riesz–Thorin and Marcinkiewicz
interpolation, the Hilbert transform, Calderón–Zygmund theory.

## Singular integrals: real-variable methods as written proofs

Mathlib does not contain the Hardy–Littlewood maximal inequality, so
`examples/singular_integrals.py` proves it, following Stein (*Singular Integrals*, ch. I §1), as a
chain of PyLeanX written proofs over the `pyleanx.realvar` vocabulary (intervals, |E|, finite
families, ⋃, ∫ over a set, ⊆): (1) Vitali's covering lemma for finitely many intervals,
(2) integrals over disjoint intervals, (3) the covering bound α|⋃Iᵢ| ≤ 4‖f‖₁, (4) the maximal
inequality on compact sets, (5) the weak type (1,1) inequality on measurable sets of finite
measure. Each cites Mathlib facts (Vitali's selection, compactness, inner regularity,
subadditivity) and the earlier theorems; Lean checks every step
(`examples/lecture_singular_integrals.ipynb`). `examples/marcinkiewicz.py` continues with the
Lᵖ bound (Stein Thm I.1(c)): p∫₀^∞ t^{p−1}μ{Mf > t} dt ≤ (8p·2^{p−1}/(p−1))∫|f|^p, whose left side
is ‖Mf‖_p^p by the layer-cake formula; the proof integrates theorem 8 over t and swaps the
order of integration (Tonelli), as in the book.

## Abstract structures: "let G be a group"

```python
from pyleanx import algebra as alg

G = alg.group("G")                    # also alg.abelian_group, alg.ring, alg.comm_ring, alg.field
a, b, x = pl.symbols("a b x", G)

abelian = pl.Theorem(
    "abelian_of_sq_eq_one", [a, b],
    assumptions={"h": pl.Forall(x, x * x == 1)},
    conclusion=a * b == b * a,
    proof=pl.proof(
        pl.claim(pl.Forall(x, alg.inv(x) == x), because=[alg.inv_eq_of_mul_eq_one, "h"],
                 name="self_inverse"),
        pl.chain(a * b,
                 ("=", alg.inv(a * b), "self_inverse"),
                 ("=", alg.inv(b) * alg.inv(a), alg.mul_inv_rev),
                 ("=", b * a, "self_inverse")),
    ),
)
```

The theorem is stated for every group (Lean: `{G : Type*} [Group G]`). Any Lean type
class works: `pl.type_param("V", "AddCommGroup", label="abelian group")`.

## Vocabulary

* `pyleanx.numbers` (`nt`): `divides`, `even`, `odd`, `prime`, `factorial`, `gcd`; facts
  such as `even_or_odd`, `even_iff_two_mul`, `exists_prime_dvd`, `dvd_factorial`,
  `dvd_add_right`, `prime_dvd_mul` (Euclid's lemma).
* `pyleanx.analysis` (`an`): `tendsto(a, L)` for sequences, with `an.tendsto_iff`
  (the ε–N definition, shipped with its proof) and `an.triangle_inequality`; `deriv`,
  `differentiable` and calculus facts; `sin`, `cos`, `exp`, `log`, `sqrt`.
* `pyleanx.algebra` (`alg`): abstract `group`/`ring`/`field`, `inv`, group facts
  (`mul_inv_rev`, `inv_eq_of_mul_eq_one`, `mul_left_cancel`, …); inequalities.
* `pyleanx.complex_analysis` (`ca`): `C` (ℂ), `I`, `two_pi_i`, `ball`, `closed_ball`,
  `sphere`, `mem`, `holomorphic_on`, `differentiable_at`, `continuous_on`,
  `difference_quotient`, `circle_integral`; Cauchy's theorem for a disc
  (`ca.cauchy_theorem`), `ca.kernel_integral` (∮ dz/(z − w) = 2πi), and
  `ca.INTEGRAL_FORMULA` (Mathlib's own statements of the formula, to `avoid=`).
* `pyleanx.geometry` (`geo`): points, `dist`, `angle`, `line`, `parallel`,
  `on_segment`, `triangle`, `similar`, `similar_AA`, `corresponding_angles`, `similar_sides`.

Anything else in Mathlib is reachable through `pl.const`/`pl.app`, `pl.mathlib` and
`pl.type_param`, with a less readable display.

## Proving a known fact without using it: `avoid=`

Mathlib's `simp` already knows sin²x + cos²x = 1. A "proof" of that identity that lets the
automation use it is circular, even though Lean would accept it. Name the lemmas a proof
must not use:

```python
from pyleanx import analysis as an

x, t = pl.symbols("x t", pl.Real)
f = pl.symbol("f", pl.Fn(pl.Real, pl.Real))

pythagorean_identity = pl.Theorem(
    "pythagorean_identity", [x],
    conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
    avoid=[an.sin_sq_add_cos_sq, an.cos_sq_add_sin_sq],
    proof=pl.proof(
        pl.let(f, lambda t: an.sin(t)**2 + an.cos(t)**2),
        pl.claim(an.differentiable(f), note="sin and cos are differentiable"),
        pl.claim(pl.Forall(t, an.deriv(f, t) == 0), because=[an.deriv_sin, an.deriv_cos],
                 note="f′(t) = 2 sin t cos t − 2 cos t sin t = 0"),
        pl.claim(f(x) == f(0), because=an.constant_of_zero_derivative),
        pl.claim(f(0) == 1, because=[an.sin_zero, an.cos_zero]),
        pl.conclude(),
    ),
)
```

`avoid=` does two things:

1. the gap-filling automation is told not to use those lemmas (`simp [-lemma]`, and `aesop`
   is not tried, since its rule set cannot be restricted here);
2. a Lean check after the theorem walks the proof term (including Lean's auxiliary
   declarations) and **fails verification** if it refers to any of them anyway.

An avoided lemma's module is imported (so it can be named), and the check also looks inside
the PyLeanX facts the proof cites, so a shipped fact cannot use an avoided lemma either.
`readable_cauchy_integral.py` proves Cauchy's integral formula while avoiding Mathlib's own
formula and its removable-singularity theorem, which Mathlib derives from the formula.

Without `avoid=`, the step "f(0) = 1" above is proved by `simp` *using* sin²+cos²=1. The
check catches exactly that. It checks the proof you wrote: lemmas the proof cites may
themselves depend on the avoided fact deep inside Mathlib (use `pl.proof_graph` to see a
lemma's foundations).

## Facts PyLeanX ships

Some textbook facts are not in Mathlib in a form a proof can cite. PyLeanX ships them as
Lean theorems **with their proofs** (`geo.corresponding_angles`, `geo.similar_sides`,
`an.tendsto_iff`). A Lean file that cites one contains its full proof, so Lean checks it on
every run and its axioms are part of your theorem's audit. Nothing is taken on trust.

## Using a proved theorem

Once a theorem is proved, cite the theorem **object** in later proofs, exactly like a library
fact. From `examples/using_cauchy_integral.py`:

```python
from readable_cauchy_integral import cauchy_integral_formula   # the proved theorem

zero, one, two = pl.ascribe(0, ca.C), pl.ascribe(1, ca.C), pl.real(2)

contour_integral = pl.Theorem(
    "contour_integral_z_sq", [],
    conclusion=ca.circle_integral(lambda z: pl.smul(ca.inv(z - one), z**2), zero, two)
    == ca.two_pi_i(),
    proof=pl.proof(
        pl.claim(ca.holomorphic_on(pl.fun(lambda z: z**2, ca.C), ca.closed_ball(zero, two)),
                 name="hf", note="z ↦ z² is a polynomial"),
        pl.claim(ca.mem(one, ca.ball(zero, two)), name="hw", note="|1 − 0| = 1 < 2"),
        pl.chain(ca.circle_integral(lambda z: pl.smul(ca.inv(z - one), z**2), zero, two),
                 ("=", pl.smul(ca.two_pi_i(), one**2), cauchy_integral_formula),
                 ("=", ca.two_pi_i(), None, "1² = 1")),
    ),
)
```

```text
3. ∮_(|z - 0| = 2)(z - 1)⁻¹ z² dz = (2 · π · i) 1² (theorem cauchy_integral_formula)
                                   = 2 · π · i (1² = 1).
✔ Checked by Lean (axioms: propext, Classical.choice, Quot.sound).
```

The gap filler instantiates the theorem (f = z ↦ z², c = 0, w = 1, R = 2) and discharges its
hypotheses with steps 1 and 2.

### Citing the proved theorem, never an unproved one

* **Cite the object, not a string.** `because=cauchy_integral_formula` (or
  `pl.cite(cauchy_integral_formula)`) carries the theorem *with its proof*. The Lean file for
  the citing theorem contains the cited theorem and its proof first, so Lean re-checks it on
  every run. A string `"cauchy_integral_formula"` is only a name: it is not re-checked and
  could even resolve to a different Lean declaration.
* **An unproved theorem cannot be cited.** If the cited theorem has no proof, PyLeanX refuses
  to build the Lean file (`… cites theorem draft, which has no proof; prove it first`).
* **A wrong proof cannot hide behind a citation.** If the cited proof fails, every theorem
  that cites it is rejected (*the cited theorem … was not accepted by Lean*); theorems in the
  same run that do not cite it are unaffected. Its axioms are part of the citing theorem's
  audit, and `avoid=` checks look inside it too.
* **Banked theorems.** `bank.add_theorem(thm, result, id=…)` stores only *verified*
  theorems, with their evidence (axioms, toolchain, Mathlib revision) and the theorems they
  cite as dependencies. `bank.load(id)` rebuilds the theorem exactly (hash-checked) and makes
  it citable; `bank.load_with_dependencies(id)` loads what it cites first. A loaded theorem is
  cited like any other, so its proof is re-checked again where it is used.

## Reading a proof back

`thm.prose(result)` (or `pl.prose(thm, result)`) returns the proof as numbered steps:
`print` it for text, or display it in Jupyter for typeset mathematics. It reports *Checked
by Lean* only for a `verified` result. It is a view of the same steps Lean checked: every
printed step is a Lean step in `thm.to_lean()` with the same number (`step6_2` is 6.2),
and `pl.explain(thm)` shows the goals before and after each one.

## Limits

* The gap filler is standard automation, not a referee: a step a mathematician accepts may
  still be too big. Smaller steps or a cited fact usually fix it.
* Each area needs its vocabulary. The modules above cover the examples and their
  neighbourhood (elementary number theory, sequences, groups, plane geometry, calculus);
  other areas work through `pl.const`/`pl.type_param` with plainer display.
* Prose rendering is display only. Lean checks the expressions, never the text. Notes are
  not checked (a wrong note is only a wrong comment).
* The generated Lean is long, because each step lists the automation it tries.

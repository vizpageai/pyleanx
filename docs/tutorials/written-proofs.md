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
  known, or use the half of it the step needs (one side of an `∧`, one direction of an `↔`);
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

Without `avoid=`, the step "f(0) = 1" above is proved by `simp` *using* sin²+cos²=1. The
check catches exactly that. It checks the proof you wrote: lemmas the proof cites may
themselves depend on the avoided fact deep inside Mathlib (use `pl.proof_graph` to see a
lemma's foundations).

## Facts PyLeanX ships

Some textbook facts are not in Mathlib in a form a proof can cite. PyLeanX ships them as
Lean theorems **with their proofs** (`geo.corresponding_angles`, `geo.similar_sides`,
`an.tendsto_iff`). A Lean file that cites one contains its full proof, so Lean checks it on
every run and its axioms are part of your theorem's audit. Nothing is taken on trust.

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

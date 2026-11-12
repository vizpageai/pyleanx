# Writing proofs the way mathematicians do

A proof in a textbook is a list of statements, each with a reason: *"DE ∥ BC, so ∠ABC =
∠ADE (corresponding angles). Hence △ABC ∼ △ADE (AA)…"*. PyLeanX lets you write exactly
that, and Lean checks every step.

```python
import pyleanx as pl
from pyleanx import geometry as geo

A, B, C, D, E = geo.points("A B C D E")

side_splitter = pl.Theorem(
    "side_splitter_similar", [A, B, C, D, E],
    assumptions={
        "hABC": geo.triangle(A, B, C),
        "hD": geo.on_segment(D, A, B),
        "hE": geo.on_segment(E, A, C),
        "hP": geo.parallel(geo.line(D, E), geo.line(B, C)),
    },
    conclusion=geo.dist(A, D) / geo.dist(A, B) == geo.dist(A, E) / geo.dist(A, C),
    proof=pl.proof(
        pl.claim(geo.angle(A, B, C) == geo.angle(A, D, E), because=geo.corresponding_angles),
        pl.claim(geo.angle(B, C, A) == geo.angle(D, E, A), because=geo.corresponding_angles_2),
        pl.claim(geo.similar((A, B, C), (A, D, E)), because=geo.similar_AA),
        pl.conclude(because=geo.similar_sides),
    ),
)
result = side_splitter.verify()
print(side_splitter.prose(result))
```

```text
Theorem (side_splitter_similar). For all A, B, C, D, E ∈ ℝ²: if ABC is a triangle,
D ∈ segment AB, E ∈ segment AC, DE ∥ BC, then |AD|/|AB| = |AE|/|AC|.
Proof.
  1. ∠ABC = ∠ADE.  (corresponding angles (DE ∥ BC))
  2. ∠BCA = ∠DEA.  (corresponding angles (DE ∥ BC))
  3. △ABC ∼ △ADE.  (AA similarity)
  Hence |AD|/|AB| = |AE|/|AC| (similar triangles have proportional sides). ∎
  ✔ Checked by Lean (axioms: propext, Classical.choice, Quot.sound).
```

## The three steps

| Python | Meaning | Lean |
|---|---|---|
| `pl.let(f, lambda t: …)` | *Let f(t) = …* | `set f : ℝ → ℝ := fun t => … with f_def` |
| `pl.claim(P, because=facts, note="…")` | *P holds, because of these facts* | `have stepN : P := by …` |
| `pl.conclude(because=facts, note="…")` | *Hence the theorem* | closes the goal |

* **`because`** is a fact or a list of facts: library facts (`geo.similar_AA`,
  `an.constant_of_zero_derivative`, anything in `pl.mathlib`), hypotheses (`"hP"`), named
  earlier claims, or other theorems. Everything proved so far is always available and does
  not need to be cited.
* **`note`** is the reason in words, shown when the proof is printed. Lean ignores it.
* Claims are named `step1`, `step2`, … in order; pass `name="h"` to cite one by name.
* The gap between the cited facts and the claim is filled by standard automation:
  applying a cited fact and discharging its side conditions from what is known,
  `simp`/`norm_num` with the facts, `linarith`/`nlinarith`, `field_simp`, `fun_prop`,
  `positivity`, and the same after unfolding `pl.let` definitions and introducing `∀`
  variables. Each attempt must close the claim completely; nothing is assumed. If no
  attempt works, Lean reports an error at that claim and the proof is not verified: split
  the step into smaller claims, cite the missing fact, or give `proof=` an explicit tactic.

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
check catches exactly that. It is a check on the proof you wrote: lemmas the proof cites
may themselves depend on the avoided fact deep inside Mathlib (use `pl.proof_graph` to see
a lemma's foundations).

## Facts PyLeanX ships

Some textbook facts are not in Mathlib in a form a proof can cite. PyLeanX ships them as
Lean theorems **with their proofs** (`geo.corresponding_angles`, `geo.corresponding_angles_2`,
`geo.similar_sides`). A Lean file that cites one contains its full proof, so Lean checks it
on every run and its axioms are part of your theorem's audit. Nothing is taken on trust.

## Reading a proof back

`thm.prose(result)` (or `pl.prose(thm, result)`) returns the proof as numbered steps:
`print` it for text, or display it in Jupyter for typeset mathematics. It reports *Checked
by Lean* only for a `verified` result. It is a view of the same steps Lean checked: every
printed claim is a `have` in the Lean source (`thm.to_lean()`), and `pl.explain(thm)` shows
the goals before and after each one.

Examples: `examples/readable_trig.py`, `examples/readable_side_splitter.py`,
`examples/readable_am_gm.py`.

## Limits

* The gap filler is standard automation, not a mathematician: a step a referee accepts may
  still be too big. Smaller claims or a cited fact usually fix it.
* The vocabulary covers what the examples need: derivatives and differentiability of
  real functions; lines, segments, parallels, triangles and similarity in the plane.
  Anything else is reachable through `pl.const`/`pl.app` and `pl.mathlib`, with less
  readable display.
* Prose rendering is display only. Lean checks the expressions, never the text.

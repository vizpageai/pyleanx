# Any Lean vocabulary: types, functions, definitions, structured proofs

The first tutorials used PyLeanX's built-in numbers and functions. This page shows how to
state and prove results about *anything* Lean and Mathlib can express (vectors, functions,
sums, integrals, your own definitions and structures) and how to write proofs as a sequence
of mathematical steps. Every block runs in order and is checked against real Lean in the
project's tests.

## Any type

Built-in sorts (`pl.Real`, `pl.Nat`, …) are checked by Python. Every other Lean type is an
*open* type: Python records it and Lean checks how it is used.

```python
import pyleanx as pl

V = pl.EuclideanSpace(3)                 # ℝ³ with its norm and inner product
F = pl.Fn(V, pl.Real)                    # functions ℝ³ → ℝ
c = pl.var("c", pl.Real)
x = pl.var("x", V)
f = pl.var("f", F)

print(pl.norm(pl.smul(c, x)) == pl.norm(c) * pl.norm(x))    # ‖c • x‖ = ‖c‖ * ‖x‖
print(f(x) + 1)                                                # f x + 1
print(pl.Type("Set ℝ"), pl.Prod(V, V), pl.Fin(3))
```

`pl.Type("…")` accepts any Lean type text (checked so it cannot break out of its place in
the generated file).

## Functions, sums and integrals

`fun`, `∑` and `∫` take a Python function and call it once with a fresh bound variable:

```python
n = pl.var("n", pl.Nat)
square = pl.fun(lambda t: t**2 + 1, pl.Real)                 # fun t => t ^ 2 + 1
coords = pl.sum(pl.Fin(3), lambda i: x(i)**2)                 # ∑ i : Fin 3, x i ^ 2
area = pl.integral(lambda t: t**2, bounds=(0, 1))             # ∫ t in 0..1, t ^ 2
odd = pl.sum(pl.const("Finset.range", imports=["Mathlib.Data.Finset.Range"])(n),
             lambda i: 2 * i + 1, sort=pl.Nat)               # ∑ i ∈ range n, (2i + 1)
print(odd.to_lean())
```

Any Mathlib declaration can be used by name with `pl.const` (or, better, through generated
bindings, see [Libraries](libraries.md)).

## Definitions and structures

```python
Vec = pl.define_type("TutVec", V)        # abbrev TutVec : Type := EuclideanSpace ℝ (Fin 3)

@pl.define(returns=pl.Real)
def tut_q(v: Vec):
    """Relativistic energy per unit mass."""
    return pl.sqrt(1 + pl.norm(v)**2)

@pl.structure
class TutPoint:
    px: pl.Real
    py: pl.Real

v = pl.var("v", Vec)
p = pl.var("p", TutPoint)
print(tut_q(v), p.px, pl.mk(TutPoint, px=1, py=2))
```

Definitions become Lean `def`/`abbrev`/`structure` declarations placed before the theorems
that use them. Lean checks them together; if a definition does not elaborate, every theorem
in that file is rejected.

## Proofs as mathematical steps

`pl.have` states an intermediate fact, `pl.calc` a chain of relations, and each step is
closed by `pl.auto()` unless you give a proof. `pl.auto` tries the standard closing
tactics (rfl, ring, norm_num, simp, linarith, positivity, nlinarith, field_simp, aesop), and
each attempt must finish the goal completely.

```python
one_le_q = pl.Theorem(
    "tut_one_le_q", [v], conclusion=pl.Le(1, tut_q(v)),
    proof=pl.proof(
        pl.unfold(tut_q),
        pl.have("h", pl.Le(1, 1 + pl.norm(v)**2), pl.auto(pl.ref("sq_nonneg")(pl.norm(v)))),
        pl.exact(pl.ref("Real.one_le_sqrt.mpr")("h"))))

a, b = pl.symbols("a b", pl.Real)
parallelogram = pl.Theorem(
    "tut_square_bound", [a, b], conclusion=(a + b)**2 <= 2 * (a**2 + b**2),
    proof=pl.calc((a + b)**2,
                  ("=", a**2 + 2*a*b + b**2),
                  ("<=", a**2 + (a**2 + b**2) + b**2, pl.nlinarith(pl.ref("sq_nonneg")(a - b))),
                  ("=", 2 * (a**2 + b**2))))

odd_sum = pl.Theorem(
    "tut_sum_odd", [n], conclusion=odd == n**2,
    proof=pl.induction("n", zero=pl.simp(),
                       succ=pl.rw(pl.ref("Finset.sum_range_succ",
                                         ["Mathlib.Algebra.BigOperators.Group.Finset.Basic"]),
                                  "ih") >> pl.ring()))

results = pl.verify_all([one_le_q, parallelogram, odd_sum], timeout=1800)
for r in results:
    print(r.summary())
assert all(r.verified for r in results)
```

Also available: `pl.obtain("x hx", h)` (unpack ∃/∧), `pl.cases(h, "h1", "h2")` (split ∨),
`pl.show(P)`, `pl.ext("i")`, `pl.use(witness)`.

## Let PyLeanX find the step

`thm.auto_prove(*hints)` tries the automation strategies as separate candidates in one Lean
run and attaches the first that Lean verifies, as an explicit, reproducible proof:

```python
t = pl.Theorem("tut_auto", [a, b], conclusion=2*a*b <= a**2 + b**2)
attempt = t.auto_prove(pl.ref("sq_nonneg")(a - b), timeout=1800)
print(attempt.status, attempt.script)
assert attempt.verified
```

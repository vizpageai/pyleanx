# Writing a certifier

A step of a written proof (`pl.claim(P, because=[...])`) is closed by a list of tactics
that Lean tries in turn: Lean searches, within its time budget. A **certifier** moves the
search to Python. It sees the mathematics of the step (what it states, what is in scope),
searches with any Python tool, and returns a *certificate*: a tactic that Lean only has to
check. Nothing a certifier returns is trusted. If the certificate is wrong, Lean rejects
it and the ordinary alternatives still run; `verified` still means that Lean's kernel
checked the proof and the axiom audit passed.

## The certifiers PyLeanX ships

`pip install 'pyleanx[certify]'` (sympy and scipy), then:

```python
import pyleanx as pl
import pyleanx.certifiers          # registers them; pyleanx.certifiers.disable() removes them

a, b, c = pl.symbols("a b c", pl.Real)
amgm = pl.Theorem(
    "am_gm_three", [a, b, c],
    assumptions={"ha": a >= 0, "hb": b >= 0, "hc": c >= 0},
    conclusion=a**3 + b**3 + c**3 >= 3 * a * b * c,
    proof=pl.proof(pl.claim(a**3 + b**3 + c**3 >= 3 * a * b * c,
                            because=["ha", "hb", "hc"], name="h"),
                   pl.conclude(because="h")))

for certifier, tactic in amgm.derivation().certificates("h"):
    print(certifier, ":", tactic[:90], "…")
```

The inequality certifier found a sum of nonnegative terms equal to the gap,

    a³ + b³ + c³ − 3abc = a·(a − c)² + b·(b − c)² + (3/2)·c·(a − b)² + …

and wrote it as one `linear_combination`. Lean's own search (`nlinarith`, `positivity`,
`grind`) does not find this proof within the default budget; with the certificate Lean
checks it at once:

```python
result = amgm.verify()
assert result.verified
print(result.axioms)               # ('propext', 'Classical.choice', 'Quot.sound')
```

| certifier | proves | certificate Lean checks |
|---|---|---|
| `polynomial` | `P = Q` from cited equalities (ℕ, ℤ, ℚ, ℝ) | `linear_combination c₁ * h₁ + …` |
| `inequality` | `≤ < ≥ >` and `False`, from cited (in)equalities | `linear_combination λ₁ * h₁ + λ₂ * sq_nonneg (a - b) + …` |
| `witness` | `∃ x, P x` | `exact ⟨w, (by …), …⟩` |
| `divisibility` | `a ∣ b` over ℕ and ℤ | `exact ⟨q, by linear_combination …⟩` |

Terms that are not ring arithmetic (`Real.sin x`, `√x`, `x / y`) are treated as opaque
atoms, and `x / y` as `x * y⁻¹` with `y * y⁻¹ = 1` from a fact `y ≠ 0` or `y > 0`. So the
same certifiers apply in trigonometry, analysis or number theory whenever the step is
algebraic in such terms. On 28 test steps from eight areas, Lean proves 14 with its own
search and all 28 with certificates (see [The core](../core.md)).

## Writing your own

A certifier is a function of a `justify.Goal`:

| field | what it is |
|---|---|
| `goal.statement` | what the step proves (a PyLeanX expression) |
| `goal.given` | `(Lean name, statement)` of the cited hypotheses and steps |
| `goal.context` | everything named in scope, cited or not |
| `goal.usable` | `given`, or `context` when nothing is cited |
| `goal.certify(sub)` | the other certifiers' certificates for a sub-goal |

It returns tactic text, a list of alternatives, or `None`. Here is a small one: for an
inequality between expressions in two real variables, it proposes `nlinarith` with the
square of their difference as a hint.

```python
from pyleanx import justify
from pyleanx.expr import Compare
from pyleanx.ops import free_vars

def square_hint(goal: justify.Goal):
    stmt = goal.statement
    if not (isinstance(stmt, Compare) and stmt.op in ("le", "lt", "ge", "gt")):
        return None
    vs = free_vars(stmt)
    if len(vs) != 2:
        return None
    x, y = vs
    return f"nlinarith [sq_nonneg ({x.name} - {y.name})]"

justify.register_certifier("square-hint", square_hint, priority=50)

u, v = pl.symbols("u v", pl.Real)
step = pl.Theorem("two_uv", [u, v], conclusion=2 * u * v <= u**2 + v**2,
                  proof=pl.proof(pl.claim(2 * u * v <= u**2 + v**2, name="h"),
                                 pl.conclude(because="h")))
assert ("square-hint", "nlinarith [sq_nonneg (u - v)]") in \
    step.derivation().certificates("h")
justify.unregister_certifier("square-hint")
```

Three rules make a certifier safe to use:

* **Deterministic.** The generated Lean is fingerprinted, so the same step must give the
  same certificate.
* **Cheap to reject.** A certificate that fails costs Lean one failed alternative. Return
  `None` rather than a guess that is usually wrong.
* **Never needed for soundness.** Lean checks every certificate. A certifier can only add
  proofs, never accept a false step.

## In a domain package

A domain package registers its certifiers through its pack, so they apply only to theorems
that use the pack's vocabulary. It can also declare which of its terms Lean's
`positivity` proves nonnegative, for the inequality certifier to use:

```py
measure = pl.domain_pack("measure", symbols=("MeasureTheory.",))
measure.certifier("measure.additivity", additivity_certificate,
                  imports=("Mathlib.MeasureTheory.Measure.MeasureSpace",))
measure.nonneg("MeasureTheory.Measure.real")
```

When you are done experimenting, unregister the shipped certifiers again (the Lean a
proof generates depends on which certifiers are registered):

```python
pyleanx.certifiers.disable()
```

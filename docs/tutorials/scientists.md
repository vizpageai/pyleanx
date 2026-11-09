# Checking derivations (for scientists and engineers)

Papers, models and code rest on algebraic steps and inequalities: a rearranged formula, a
bound used in an error estimate, a positivity condition. PyLeanX checks such steps
*exactly*: symbolic, no floating point, with a machine-checked proof. All code on this
page runs in order.

```python
import pyleanx as pl

a, b, m, x, y = pl.symbols("a b m x y", pl.Real)
```

## Rearranging a formula

The spread of two measurements around their mean equals half the squared difference:

$$ (a - \tfrac{a+b}{2})^2 + (b - \tfrac{a+b}{2})^2 = \tfrac{(a-b)^2}{2} $$

```python
mean = (a + b) / 2
spread = pl.Theorem("two_point_variance", [a, b],
                    conclusion=(a - mean)**2 + (b - mean)**2 == (a - b)**2 / 2,
                    proof=pl.ring())
```

`ring` decides polynomial identities, including division by numerals.

## A bound with conditions

If 0 < x ≤ y then x² ≤ y², a typical monotonicity step:

```python
monotone = pl.Theorem("square_monotone", [x, y],
                      assumptions={"hx": x > 0, "hxy": x <= y},
                      conclusion=x**2 <= y**2,
                      proof=pl.nlinarith())
```

## Proof text from elsewhere

Sometimes the proof comes as Lean text, from a colleague, a paper's appendix or a language
model. PyLeanX treats it as **untrusted**: refused unless you opt in, screened for
commands, then checked and audited like any other proof.

```python
geometric = pl.Theorem("am_gm_halves", [x, y],
                       conclusion=x * y <= (x**2 + y**2) / 2,
                       proof=pl.raw_tactic("nlinarith [sq_nonneg (x - y)]",
                                           imports=["Mathlib.Tactic.Linarith"]))

import dataclasses
project = pl.find_project()
lenient = project.with_(policy=dataclasses.replace(project.policy, allow_raw_tactics=True))
```

## A lower bound for a quadratic loss

Completing the square shows x² − 2mx ≥ −m² for every x and m:

```python
loss = pl.Theorem("quadratic_loss_lower_bound", [x, m],
                  conclusion=x**2 - 2*m*x >= -m**2,
                  proof=pl.nlinarith(pl.ref("sq_nonneg")(x - m)))
```

## Checking everything, reproducibly

```python
results = pl.verify_all([spread, monotone, geometric, loss], project=lenient)
for r in results:
    print(r.summary())
assert all(r.verified for r in results)
```

Each result records what was checked and how:

```python
r = results[0]
print(r.toolchain, r.mathlib_revision[:12])
print(r.fingerprint[:16])          # hash of statement, proof, Lean source, versions, policy
record = r.to_json()               # stable schema (schema_version 1): archive it with your data
```

Store `record` next to your results. Anyone with the same PyLeanX release can re-run the
check and compare fingerprints.

## From the command line

Put theorems in a script with a module-level `THEOREMS = [...]` list, then:

```bash
pyleanx check derivations.py           # exit 0 only if every theorem is verified
pyleanx check derivations.py --json    # machine-readable, e.g. for CI
```

Adding `pyleanx check` to your project's continuous integration keeps a paper's or a
model's derivations checked as the code evolves.

## Limits to keep in mind

- Statements are about exact mathematical objects (ℝ, ℚ, ℤ, ℕ). Checking a derivation does
  not check a floating-point implementation of it.
- Automation is strongest for polynomial identities (`ring`), linear inequalities
  (`linarith`), positivity, and nonlinear inequalities with a hint (`nlinarith`).
  Calculus beyond the provided lemmas currently needs Mathlib knowledge.
- Units and dimensions are not modelled; encode them in names or assumptions.

# Your first theorem

This tutorial is for mathematicians who know Python a little and Lean not at all. It takes
about 15 minutes. Every code block runs as written, in order, in one Python session or
notebook (this page is executed in the project's test suite against real Lean).

## Symbols and statements

Variables carry a *sort*: `pl.Real` (ℝ), `pl.Rat` (ℚ), `pl.Int` (ℤ), `pl.Nat` (ℕ) or
`pl.Prop` (propositions).

```python
import pyleanx as pl

x, y = pl.symbols("x y", pl.Real)
statement = (x + y)**2 == x**2 + 2*x*y + y**2
print(statement)
```

`==` did not compute anything: it built the *proposition* (x + y)² = x² + 2xy + y². In
Jupyter, `statement` alone displays it typeset.

## A theorem and a proof

A theorem is a name, the variables it quantifies over, optional assumptions, a conclusion,
and a proof. Proofs are Lean *tactics*; `pl.ring()` proves identities in commutative rings.

```python
thm = pl.Theorem("square_identity", [x, y], conclusion=statement, proof=pl.ring())
print(thm.to_lean())
```

`to_lean()` shows exactly what Lean will check:

```lean
theorem square_identity (x y : Real) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
```

## Asking Lean

```python
result = thm.verify()
print(result.summary())
assert result.verified
print(result.axioms)
```

`verify()` writes the Lean file, runs the pinned Lean on it, and audits which axioms the
proof uses. The standard ones are `propext`, `Classical.choice` and `Quot.sound`; anything
else (in particular `sorryAx`) means *not verified*.

## Assumptions

Assumptions are named hypotheses. Tactics such as `linarith` (linear arithmetic) use them.

```python
a, b = pl.symbols("a b", pl.Real)
sum_pos = pl.Theorem("sum_pos", [a, b],
                     assumptions={"ha": a > 0, "hb": b > 0},
                     conclusion=a + b > 0,
                     proof=pl.linarith())
print(sum_pos.to_latex())
```

Positivity of an expression built from squares and positive terms: `pl.positivity()`.

```python
sq = pl.Theorem("shifted_square", [x], conclusion=(x - 1)**2 + 1 > 0, proof=pl.positivity())
```

## When a proof is wrong

Lean says so, and PyLeanX tells you where.

```python
wrong = pl.Theorem("square_pos", [x], conclusion=x**2 > 0, proof=pl.positivity())
bad = wrong.verify()
assert not bad.verified
print(bad.status.value)
print(bad.errors[0].message.splitlines()[0])
```

The statement is false for x = 0, so no tactic can prove it. Fix the *statement*:

```python
fixed = pl.Theorem("square_nonneg", [x], conclusion=x**2 >= 0, proof=pl.positivity())
```

## Many theorems at once

Lean spends most of its time loading Mathlib, so check theorems together:

```python
results = pl.verify_all([sum_pos, sq, fixed])
for r in results:
    print(r.summary())
assert all(r.verified for r in results)
```

## Logic and natural numbers

```python
P = pl.prop_symbol("P")
imp = pl.Theorem("p_implies_p", [P], conclusion=pl.Implies(P, P),
                 proof=pl.intro("h") >> pl.exact("h"))      # tactics in sequence

n = pl.symbol("n", pl.Nat)
add_zero = pl.Theorem("nat_n_add_zero", [n], conclusion=n + 0 == n, proof=pl.simp())

assert all(r.verified for r in pl.verify_all([imp, add_zero]))
```

!!! tip "Theorem names must be new"
    Lean and Mathlib already use names like `imp_self`, `add_zero` or `sq_nonneg`. Reusing
    one gives "has already been declared"; pick a distinctive name.

## The decorator form

```python
@pl.theorem(proof=pl.nlinarith(pl.ref("sq_nonneg")(x - y)))
def two_xy_le(x: pl.Real, y: pl.Real):
    """2xy ≤ x² + y²."""
    return 2*x*y <= x**2 + y**2

print(two_xy_le.to_lean())
```

`pl.ref("sq_nonneg")(x - y)` cites the Mathlib lemma `sq_nonneg` at `x - y` as a hint.
Finding such lemmas is the subject of [Using Mathlib](mathlib.md).

## Notation rules worth knowing

| You write | Meaning / why |
|---|---|
| `x == y`, `x <= y` | build propositions, never `True`/`False` |
| `pl.And(p, q)`, `p & q` | conjunction (`and`, `or`, `not` raise an error: they would ask Python for a truth value) |
| `pl.And(0 <= x, x <= 1)` | instead of the chained `0 <= x <= 1` |
| `pl.Le(0, x)` | keeps the order as written (Python turns `0 <= x` into `x >= 0`; same proposition) |
| `pl.rat(1, 3)`, `pl.real("0.1")` | exact numbers; Python floats are refused, `1/3` is evaluated by Python first |
| `pl.cast(n, pl.Real)` | explicit conversion; mixing sorts is an error, never silent |
| `n - m` on `pl.Nat` | truncated subtraction, exactly as in Lean |

## Next

- [Using Mathlib](mathlib.md): analysis, geometry, citing and finding theorems.
- [Interactive proving](interactive.md): see the goals and try tactics one at a time.

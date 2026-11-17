# Fast feedback and natural steps

This page is about writing a proof the way it is written on paper, and finding out quickly
whether Lean accepts it. Everything below works with the written-proof style of
[Writing proofs like a mathematician](written-proofs.md).

## Check in seconds: `thm.check()`

`thm.verify()` starts a fresh Lean process every time. On a laptop that means loading
Mathlib (minutes) and re-checking every shipped fact and cited theorem. While you are
writing, use

```python
res = thm.check()            # or pl.check_all([thm1, thm2, ...])
print(thm.prose(res))
```

`check` keeps one Lean process running. The imports are loaded once; the shipped facts and
the theorems your proof cites are checked once and remembered; after that only your theorem
is re-checked. The first call costs as much as `verify`; later calls take seconds (the
Pythagoras example: about 12 minutes the first time, 20 seconds after that).

The check is the same as `verify`'s: the same Lean source, the same attribution of errors to
steps, the same `#print axioms` audit and axiom policy. The difference is bookkeeping:
`check` results say `backend="repl"` and are not archived. Run `verify()` once at the end
to record the result with its fingerprint.

## Catch a wrong step before Lean: `thm.sanity_check()`

```python
print(thm.sanity_check())
# Step 1 looks false: with x = 0.8338, y = 0.04687 (all hypotheses hold),
# “|x + y| ≤ |x|” fails: the left side is 0.8807, the right side 0.8338.
```

The statement and each step are tried on random numbers (and random points of the plane)
that satisfy the hypotheses. A step that fails on such a sample cannot be proved as written.
It is instantaneous, needs no Lean, and proves nothing: when no counterexample is found it
says so, and when the hypotheses cannot be sampled (an exact right angle, a function, a
set) it says that nothing was checked.

## Failures in the words of the proof

When Lean rejects a proof, `thm.prose(res)` explains why under the verdict (also available
as `pl.explain_failure(thm, res)`):

```text
  ✘ Lean did not accept this proof (rejected).
    • Step 1, “xy ≥ 0” (by x > 0 (hx)): Lean could not justify it. Still to show: False.
      Hint: the step is not a linear consequence of the cited facts; cite the fact that
      supplies the missing product or inequality, or split the step in two.
```

A numeric counterexample, when there is one, comes first. A step with no reason that fails
gets suggestions: "Facts that might justify it: geo.similar_AA (AA similarity); …".

## Cite facts by what they say

A reason that contains a space is a description of a fact, not a name:

```python
pl.claim(geo.similar((B, A, C), (C, A, D)), because=["AA similarity", "hABC", "hA"])
pl.claim(AB == AD + DB, because=["segment addition", "hD"])
pl.claim(ang(A, B, C) + ang(B, C, A) + ang(C, A, B) == pi(),
         because="the angles of a triangle add up to 180°")
```

The description is matched against the printed labels and names of the facts every domain
module provides. A description that is exactly a fact's label or name selects it. If two
facts fit about equally well, the step is refused with the candidates listed, so a
description never silently picks the wrong fact. `pl.search_facts("…")` lists the best
matches and `pl.fact("…")` returns one.

## "Similarly"

```python
pl.claim(AC ** 2 == AD * AB, because=[leg_rule, "hABC", "hC", "hD", "hAD"], name="h1"),
pl.similarly("h1", exchange=(A, B), name="h2"),          # 3. |BC|² = |BD|·|BA| (similarly)
```

`similarly` repeats an earlier step with variables exchanged (`exchange=(A, B)`, or a list of
pairs) or replaced (`replace={x: -x}`): its statement, its reasons and its own proof. A cited
hypothesis is replaced by the one that states the exchanged fact (`hAD` becomes `hBD`). Lean
checks the new step in full; nothing is assumed by symmetry.

## What you do not have to write

A textbook leaves some things implicit, and so can you. When a cited fact needs one of
these as a side condition, PyLeanX supplies it (and Lean checks it):

* the vertices of a triangle are distinct;
* ∠ABC and ∠CBA are the same angle, |AB| and |BA| the same length;
* "D lies strictly between A and B" is the same as "between B and A";
* triangle ABC is triangle BAC;
* a fact may be stated the other way round (A ≠ C for C ≠ A, a = b for b = a);
* a lemma may be applied to two cited facts in either order.

## How natural are the proofs?

`python benchmarks/naturalness.py` measures the written proofs in `examples/`: steps per
proof and the share of *bookkeeping* steps (distinctness, positivity, notation, measure-theory
side conditions). With `--lean` it also checks every proof. The latest numbers are in the
[benchmark](../benchmark.md).

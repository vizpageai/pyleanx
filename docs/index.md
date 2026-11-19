# PyLeanX

**Write theorems in Python. Have them checked by the Lean 4 kernel.**

PyLeanX is a Python frontend for [Lean 4](https://lean-lang.org) and
[Mathlib](https://leanprover-community.github.io/mathlib-overview.html), the largest
library of formalised mathematics. You build statements with ordinary Python operators,
attach a proof, and PyLeanX hands the exact Lean source to the pinned Lean toolchain. Lean,
and only Lean, decides whether the proof is correct.

```python
import pyleanx as pl

x, y = pl.symbols("x y", pl.Real)
thm = pl.Theorem("square_identity", [x, y],
                 conclusion=(x + y)**2 == x**2 + 2*x*y + y**2,
                 proof=pl.ring())

result = thm.verify()          # runs Lean + an axiom audit
assert result.verified
```

## Proofs as a textbook writes them

A proof is a list of steps; each cites, by name, the facts it follows from. Lean checks
every step, and supplies what a textbook leaves implicit (the vertices of a triangle are
distinct, ∠ABC = ∠CBA, |f| is integrable when f is, …).

```python
from pyleanx import geometry as geo

median_bisects = pl.Theorem(
    "median_bisects_apex", [A, B, C, M],
    assumptions={"hABC": geo.triangle(A, B, C), "hiso": dist(A, B) == dist(A, C),
                 "hM": geo.is_midpoint(M, B, C)},
    conclusion=angle(M, A, B) == angle(M, A, C),
    proof=pl.proof(
        pl.claim(dist(B, M) == dist(C, M), because=geo.midpoint_equal_halves),
        pl.claim(geo.congruent((B, M, A), (C, M, A)), because=geo.sss, name="hcong"),
        pl.conclude(because=[geo.cpctc, "hcong"])))
print(median_bisects.prose(median_bisects.check()))
```

```text
Proof.
  1. |BM| = |CM|.  (the midpoint divides a segment into equal halves)
  2. △BMA ≅ △CMA.  (SSS)
  Hence ∠MAB = ∠MAC (corresponding parts of congruent triangles (CPCTC), by step 2). ∎
  ✔ Checked by Lean (axioms: propext, Classical.choice, Quot.sound).
```

`thm.sanity_check()` tries every step on random examples first (no Lean); `thm.check()`
keeps Lean loaded and re-checks in seconds; `thm.verify()` records the audited result.
See [Writing proofs like a mathematician](tutorials/written-proofs.md).

## Who it is for

<div class="grid cards" markdown>

- **Mathematicians**: state results in familiar notation, see them typeset in Jupyter,
  reuse Mathlib's theorems, and get a kernel-checked answer.
  [Your first theorem →](tutorials/first-theorem.md)

- **Scientists and engineers**: check the algebra and inequalities behind a model or a
  derivation, exactly (no floating point), reproducibly, from a script or notebook.
  [Checking derivations →](tutorials/scientists.md)

- **AI and ML researchers**: a gym-like proof environment, JSON tool schemas for LLMs,
  batch checking of thousands of candidates and a benchmark, all with sound verdicts.
  [Proof agents →](tutorials/ai.md)

</div>

## Why PyLeanX

| Like PyTorch… | …in PyLeanX |
|---|---|
| tensors and their operations | statements (`x**2 + 1 > 0` builds a proposition) and `pyleanx.ops` |
| autograd's record of operations | the derivation graph of a proof (`thm.derivation()`) |
| each op's derivative rule | justification rules, registered per subject (`pyleanx.justify`) |
| a backend that does the real work | Lean 4 + Mathlib does all checking |
| eager mode / `torch.compile` | `sanity_check()` and `check()` while writing / `verify()` for the record |
| torchvision, torchaudio | domain packages, e.g. [`pyleanx-analysis`](domains.md) |

## What "verified" means

`result.verified` is `True` only if the pinned Lean accepted the exact generated file
**and** an `#print axioms` audit, read at the precise line PyLeanX emitted, shows that the
proof depends only on the standard axioms. `sorry`, user-declared axioms and native code
evaluation are rejected. A Python simplifier, a mock, or "the tactic finished" never counts.
See [Trust model](security.md).

!!! warning "Read the statement"
    A kernel check certifies the **generated Lean statement**. Whether it says what you meant
    is your responsibility. `thm.to_lean()` always shows exactly what Lean checks.

## Next steps

- [Install](install.md) PyLeanX and the pinned Lean/Mathlib (one command).
- Work through the [tutorials](tutorials/first-theorem.md).
- Look things up in the [API guide](api.md) and the [Python reference](reference.md).

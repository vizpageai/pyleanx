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
| tensors and operators | symbolic expressions: `x**2 + 1 > 0` builds a proposition |
| `nn.Module` | `pl.Theorem`, `@pl.theorem` |
| a backend that does the real work | Lean 4 + Mathlib does all checking |
| eager debugging | `thm.session()`: goals and tactics step by step |
| batching | `pl.verify_all` checks many theorems in one Lean process |

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

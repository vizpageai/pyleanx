# Case study: relativistic Vlasov–Maxwell

**Source:** OpenAI's formalization of global classical solvability for the one-species
relativistic Vlasov–Maxwell system,
[`openai/math/lean/OAI/Analysis/VlasovMaxwell`](https://github.com/openai/math/tree/main/lean/OAI/Analysis/VlasovMaxwell)
(Apache-2.0, commit `4eaee87`). It is pinned to the same Lean (`v4.34.1`) and Mathlib
(`d13f23b723b8`) as PyLeanX, and its challenge file accepts exactly PyLeanX's default axioms
(`propext`, `Quot.sound`, `Classical.choice`).

| | OAI development |
|---|---|
| Size | 207 Lean files, ~90,000 lines, 3,422 lemmas |
| Main theorem | `OAI.RVM.global_classical_solution`: every admissible datum has a classical solution, smooth on finite horizons, unique among classical solutions |
| Model | structures `Datum`, `Solution`; unknowns are functions `f : ℝ × (ℝ³ × ℝ³) → ℝ`, `E, B : ℝ × ℝ³ → ℝ³`; `fderiv`, `derivWithin`, `∫`, `Lp`, `ContDiff`, compact support |

## What was ported

[`examples/vlasov_maxwell_kinematics.py`](https://github.com/vizpageai/pyleanx/blob/main/examples/vlasov_maxwell_kinematics.py)
restates the elementary layer in PyLeanX. A vector is three real symbols; `dot`, `cross`,
`norm` and `q(v) = √(1 + ‖v‖²)` are plain Python functions that build expressions:

```text
def cross(a, b):
    return (a[1]*b[2] - a[2]*b[1], a[2]*b[0] - a[0]*b[2], a[0]*b[1] - a[1]*b[0])

lagrange = pl.Theorem("vm_cross_dot_square", [*a, *b],
    conclusion=dot(cross(a, b), cross(a, b)) == dot(a, a)*dot(b, b) - dot(a, b)**2,
    proof=pl.ring())
```

| PyLeanX theorem | OAI lemma | Proof in PyLeanX |
|---|---|---|
| `vm_dot_cross_self_left`: a·(a×b) = 0 | `dot_cross_self_left` | `ring` |
| `vm_dot_cross_cycle`: a·(b×c) = b·(c×a) | `dot_cross_cycle` | `ring` |
| `vm_cross_antisymm`: a×b = −(b×a) | `cross_antisymm` | `constructor` + `ring` per component |
| `vm_cross_dot_square`: Lagrange identity | `cross_dot_square` | `ring` |
| `vm_norm_cross_le`: ‖a×b‖ ≤ ‖a‖‖b‖ | `norm_cross_le` | `rw [← Real.sqrt_mul …]`, `Real.sqrt_le_sqrt` of the squared bound |
| `vm_poynting_norm_le_energy`: ‖E×B‖ ≤ (‖E‖²+‖B‖²)/2 | `poynting_norm_le_energy` | `nlinarith`, citing the previous theorem |
| `vm_one_le_q`: 1 ≤ q(v) | `one_le_q` | `Real.one_le_sqrt.mpr` |
| `vm_q_sq`: q(v)² = 1 + ‖v‖² | `q_sq` | `Real.sq_sqrt` |
| `vm_speed_sq_lt_one`: ‖v‖²/q(v)² < 1 (speed below c) | `norm_velocity_lt_one` (squared) | `rw`, `div_lt_one`, `linarith` |

plus three helpers (‖a‖² ≥ 0, 1 ≤ 1 + ‖v‖², the squared cross bound).

**Result** (2026-11-09, real Lean, one batch run, 41 s): **12/12 verified**, axioms
`propext, Classical.choice, Quot.sound` only.

What the run showed along the way:

- The exact Mathlib statements of `Real.sqrt_mul`, `Real.sqrt_le_sqrt`, `Real.one_le_sqrt`,
  `div_lt_one` … were looked up with `pyleanx infoview` before writing the proofs.
- A first attempt proved ‖a‖² ≥ 0 with `positivity`, which cannot see through `a0 * a0`.
  Lean rejected it, **and the two theorems citing it were rejected too** (their audit showed
  `sorryAx`): a broken lemma cannot make its dependents look verified. Switching to
  `nlinarith [sq_nonneg a0, …]` fixed all three.

!!! warning "Restatements, not the OAI lemmas"
    Lean certifies the coordinate statements above. It does **not** certify that they are
    equivalent to OAI's statements about `EuclideanSpace ℝ (Fin 3)` (they are, mathematically,
    since OAI defines `dot` and `cross` by coordinates, but no Lean proof links them here).

## What PyLeanX cannot express yet

A faithful rewrite of the model and the main theorem needs features PyLeanX does not have:

| Needed | Used in OAI for | PyLeanX today |
|---|---|---|
| Vector sorts `EuclideanSpace ℝ (Fin n)` with norm, inner product, components | `Vec`, `Phase` | coordinates by hand; only `geometry.Point` (ℝ², `=`/`≠`, `dist`, `angle`) |
| Function-valued variables and `fun` | `f`, `E`, `B`, `fun y => F y i` | variables are scalars, points or propositions |
| User definitions and structures (`def`, `structure`) | `q`, `curl`, `Datum`, `Admissible`, `Classical` | Python functions can build *expressions*, but nothing becomes a named Lean definition |
| Calculus and measure theory: `fderiv`, `derivWithin`, `∫`, `∑ i : Fin 3`, `iteratedFDeriv`, `Lp`, `=ᵐ` | the equations, `rho`, `current`, energy | `sqrt`, `exp`, `log`, `sin`, `cos`, `π` only |
| Sets and predicates: `Icc`, `tsupport`, `IsCompact`, `ContDiffOn`, `HasCompactSupport`, `MemLp` | regularity and support conditions | none |
| Depending on an external Lean library | importing `OAI.…` | projects contain Mathlib only |

## The realistic path for developments like this

Rewriting 90,000 lines of Lean in Python would not add trust (Lean already checked them) and
would lose the proof engineering. The useful integration is the other direction:

1. **Depend on the library**: let a PyLeanX project `require` an external Lake package
   (here OAI) and build or fetch it.
2. **Browse it**: `pl.infoview("OAI.RVM.global_classical_solution")` and the theorem bank
   index its declarations with the statements Lean reports.
3. **Build on it**: state consequences and special cases in PyLeanX, citing OAI lemmas with
   `pl.ref`, checked with the same audit (here: the axiom allowlist already matches).
4. **Grow the IR** where users need it most: vector sorts, function variables with
   `fun`, and named definitions are the first three.

These are recorded on the [roadmap](../roadmap.md).

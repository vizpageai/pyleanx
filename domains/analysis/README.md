# PyLeanX Analysis

Real and measure-theoretic analysis for [PyLeanX](../../README.md), written as textbook
proofs and checked by Lean. A separate package built on PyLeanX's public API, the way
torchvision is built on torch: PyLeanX never imports it.

```bash
pip install -e domains/analysis        # from a PyLeanX checkout
```

```python
import pyleanx as pl
import pyleanx_analysis as an
from pyleanx_analysis import facts

f = pl.symbol("f", pl.Fn(pl.Real, pl.Real))
alpha = pl.symbol("α", pl.Real)
level = an.pred_set(lambda x: alpha <= pl.abs(f(x)), pl.Real)

markov = pl.Theorem(
    "markov_inequality", [f, alpha],
    assumptions={"hf": an.integrable(f)},
    conclusion=alpha * an.measure(level) <= an.l1_norm(f),
    proof=pl.proof(pl.conclude(because=facts.markov)),     # "by Markov's inequality"
)
print(markov.prose(markov.verify()))
```

```text
Theorem (markov_inequality). For all f ∈ ℝ → ℝ, α ∈ ℝ: if f ∈ L¹(ℝ), then
α · |{x : α ≤ |f(x)|}| ≤ ∫_ℝ |f(x)| dx.
Proof.
  Hence α · |{x : α ≤ |f(x)|}| ≤ ∫_ℝ |f(x)| dx (Markov's inequality). ∎
  ✔ Checked by Lean (axioms: propext, Classical.choice, Quot.sound).
```

Mathlib's Markov inequality needs "|f| ≥ 0 almost everywhere" and "|f| is integrable". A
textbook does not say either; with this package installed, neither does the proof.

## What the package adds

| Part | What it does |
|---|---|
| Vocabulary | `an.real` (sequences, limits, continuity, derivatives, classical theorems) and `an.integration` (Lebesgue measure, integrability, intervals, maximal averages), also at top level |
| Facts (`pyleanx_analysis.facts`) | Markov's inequality, monotonicity and additivity of the integral, \|∫f\| ≤ ∫\|f\|, the integral over a set |
| Justification rules (`rules.py`) | side conditions a textbook never writes: \|f\| integrable from f, integrability on a set or an interval, \|f\| ≥ 0 a.e., ∫\|f\| ≥ 0, compact sets and subsets of finite-measure sets have finite measure. Active only in theorems using measure-theoretic vocabulary |
| Numeric sanity checks (`numeric.py`) | random smooth functions (some integrable over ℝ, each knowing its properties); a hypothesis `∀ t, f t = e(t)` defines `f`; derivatives (Richardson extrapolation) and integrals (adaptive Simpson) to about 1e-10. A wrong derivative or a wrong value of an integral is reported with the sample |
| Explanations (`hints.py`) | failures about integrability, finiteness of measures, measurability, limits and derivatives |

## Chapter: integrals of absolute values (`pyleanx_analysis.chapters.integration`)

Each theorem is written twice, as the core alone requires (every side condition a step)
and as a textbook writes it:

| Theorem | Core style | With the analysis pack | Lean |
|---|---:|---:|---|
| Markov's inequality: α·\|{\|f\| ≥ α}\| ≤ ∫\|f\| | 3 steps | **1 step** | both verified |
| ∫ over [c − r, c + r] of \|f\| ≤ ∫\|f\| | 3 steps | **1 step** | both verified |

Verified on 2026-11-19 with the pinned Lean and Mathlib (batch check, standard axioms only:
`propext`, `Classical.choice`, `Quot.sound`): `python -m pyleanx_analysis.chapters.integration`.

## Chapter: derivatives of functions given by a formula (`pyleanx_analysis.chapters.derivatives`)

"Let f(t) = t² + 1; then f′(x) = 2x": the proof says that f is that function (from the
hypothesis, by `funext`) and differentiates the formula. The calculus pack imports the
derivative rules (sums, products, powers, sin, cos) the differentiation needs.

| Theorem | Steps | Lean |
|---|---:|---|
| f(t) = t² + 1 ⇒ f′(x) = 2x | 2 | verified |
| f(t) = sin(t)·t ⇒ f′(x) = cos(x)·x + sin(x) | 2 | verified |

`thm.sanity_check()` evaluates the derivative of the defined function numerically, so a
wrong derivative (for instance a product rule missing a term) is reported with the point.

## Tests

```bash
pytest domains/analysis/tests     # in its own process: importing a pack changes the Lean
                                  # its theorems generate, so the core's tests run without it
```

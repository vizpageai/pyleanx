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
| Numeric sanity checks (`numeric.py`) | random smooth functions (some integrable over ℝ, each knowing its properties) and random sequences (rational, alternating, geometric, oscillating); a hypothesis `∀ t, f t = e(t)` (or `∀ n, a n = e(n)`) defines `f` (or `a`); derivatives (Richardson extrapolation) and integrals (adaptive Simpson) to about 1e-10. A wrong derivative or a wrong value of an integral is reported with the sample |
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

## Chapter: the Calderón–Zygmund interval estimate (`pyleanx_analysis.chapters.calderon_zygmund`)

Stein, *Singular Integrals*, ch. I §3: if f is locally integrable, a ∈ I = [c − r, c + r]
and a ∉ {Mf > α}, then ∫_I |f| ≤ 2α|I|. The proof is Stein's: I ⊆ J = [a − 2r, a + 2r];
J has average at most α because a ∉ {Mf > α}; |J| = 2|I|. It has 9 steps; the core-only
version in PyLeanX's `examples/calderon_zygmund.py` has 16, seven of them side conditions
(f and |f| integrable on J, |f| ≥ 0 a.e., I ⊆ J a.e., 2r > 0, r ≥ 0, 2r ≥ 0) that this
package's rules now supply. Verified by Lean on 2026-11-19 (standard axioms).

## What the package removes from existing proofs

The harmonic-analysis chapters in PyLeanX's `examples/` were written for the core alone, so
they state their side conditions as steps. `benchmarks/pack_ablation.py` deletes those
steps (and the citations of them) and lets Lean decide, with this package imported, which
proofs still verify. Lean's verdicts on 2026-11-19 (local batch checks, standard axioms):

| Proof | Bookkeeping steps removed, all together | Remaining |
|---|---:|---|
| Calderón–Zygmund: average over an interval (`cz_interval_average`) | **7 of 7** (16 → 9 steps) | none |
| Hilbert kernel smoothness (`hilbert_kernel_smooth`) | **5 of 5** | none |
| The maximal function's level set is open (`maximal_level_set_open`) | **9 of 9** | none |
| Level-set bound (`maximal_level_set_bound`) | 3 of 5 | μ(K) ≠ ∞; the sign of 8‖f·1_{\|f\|>α/2}‖₁/α |
| Hardy–Littlewood weak type (`hardy_littlewood_weak_type`) | 2 of 5 (3 one at a time) | the sign of 4‖f‖₁/α; μ(K) ≠ ∞ |
| Splitting estimate, integrals over disjoint intervals | 2 of 2 each | none |

Step by step (one bookkeeping step removed at a time): the Calderón–Zygmund intervals
module loses 6 of 11 (the endpoints' 2 of 4 each, 2 of 3 in the main theorem; the steps
still needed are topological, "the complement is closed" and "the set is bounded above",
for which the package has no rules yet), the harmonic-analysis lecture 1 of 1, the Hilbert
kernel's Hörmander estimate 6 of 9 and its decay estimate 1 of 3; the steps still needed are the
integrability of kernel products such as b(w)/(x − w) on a set, which takes an argument
(continuity away from the singularity, boundedness) rather than a rule.

Two of the package's rules came from this experiment: the first run on the Calderón–
Zygmund decomposition removed 6 of the 7 steps one at a time but not all together, because
"|f| is integrable on a closed interval when f is locally integrable" and "A ⊆ B holds
almost everywhere" had no rule. With them, all 7 go.

## Tests

```bash
pytest domains/analysis/tests     # in its own process: importing a pack changes the Lean
                                  # its theorems generate, so the core's tests run without it
```

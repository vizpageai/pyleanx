# PyLeanX

[![ci](https://github.com/vizpageai/pyleanx/actions/workflows/ci.yml/badge.svg)](https://github.com/vizpageai/pyleanx/actions/workflows/ci.yml)
[![docs](https://github.com/vizpageai/pyleanx/actions/workflows/docs.yml/badge.svg)](https://vizpageai.github.io/pyleanx/)
[![PyPI](https://img.shields.io/pypi/v/pyleanx.svg)](https://pypi.org/project/pyleanx/)
[![Python](https://img.shields.io/badge/python-3.11%20%7C%203.12%20%7C%203.13-blue)](https://pypi.org/project/pyleanx/)
[![License: MIT](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE)

**Write theorems in Python. Have them checked by the Lean 4 kernel.**

📖 **Documentation: <https://vizpageai.github.io/pyleanx/>**: installation, tutorials for
mathematicians, scientists and AI researchers, and the API reference.

PyLeanX is a Python-first frontend for Lean 4 + Mathlib, built for mathematicians
and for AI/ML pipelines. Think of the PyTorch experience: symbolic objects,
operator overloading, a compile step, but here the "backend" is Lean, and
Lean alone decides whether a proof is correct.

```python
import pyleanx as pl

x, y = pl.symbols("x y", pl.Real)
thm = pl.Theorem("square_identity", variables=[x, y],
                 conclusion=(x + y)**2 == x**2 + 2*x*y + y**2)
thm.prove(pl.ring())

print(thm.to_lean())          # exact Lean source that will be checked
result = thm.verify()         # runs Lean + axiom audit
assert result.verified, result.diagnostics
print(result.axioms)          # ('propext', 'Classical.choice', 'Quot.sound')
```

Generated Lean:

```lean
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem square_identity (x y : Real) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

#print axioms square_identity
```

> **Status: alpha (0.1.0 in preparation).** Milestones M0–M8 are implemented and tested
> against real Lean; release engineering (M9) is in progress. See [docs/roadmap.md](docs/roadmap.md) for test evidence
> and known limitations. The API may still change in 0.x releases
> ([stability policy](docs/stability.md)).

## What "verified" means

`result.verified` is `True` only when **all** of these hold:

1. Lean (pinned toolchain `v4.34.1`, pinned Mathlib) accepted the exact generated
   file with no errors in the theorem.
2. An `#print axioms` report was found **at the exact line PyLeanX emitted** for that
   theorem (text printed elsewhere cannot spoof it).
3. Every axiom the proof transitively depends on is allowed by the policy: by default
   only `propext`, `Classical.choice`, `Quot.sound`. `sorryAx`, user axioms, and
   native-evaluation trust (`Lean.ofReduceBool`, …) are rejected.

The result also records the toolchain, Mathlib revision, Lean source, diagnostics with
Python file:line origins, timing, and a reproducibility fingerprint.

Python never decides truth. A mock backend, a symbolic simplifier, a finished tactic
or a zero exit code is never reported as `verified`.

## Install

Requirements: Python ≥ 3.11 and [elan](https://lean-lang.org/install/manual/) (Lean's
toolchain manager).

```bash
pip install pyleanx              # or "pyleanx[interactive]" for step-by-step proof sessions
pyleanx init                     # pinned Lean/Mathlib workspace + `lake exe cache get`
pyleanx doctor                   # check everything
```

From a checkout: `pip install -e ".[dev,interactive,docs]"`. Full instructions, including
managed Windows machines: [docs/install.md](docs/install.md).

If a security policy blocks the generated `pyleanx.exe` launcher (as on some managed
Windows machines), use `python -m pyleanx doctor`, `python -m pyleanx check ...` etc.

In a source checkout, the repository's `lean-project/` is found automatically;
otherwise `pyleanx init` creates `~/.pyleanx/lean-project`. Set `PYLEANX_PROJECT` to
use another workspace. The first `lake exe cache get` downloads several GB of prebuilt
Mathlib; nothing is rebuilt from source.

## Examples

| File | Statement | Tactic |
|---|---|---|
| [examples/square_identity.py](examples/square_identity.py) | (x+y)² = x²+2xy+y² over ℝ | `ring` |
| [examples/square_nonnegative.py](examples/square_nonnegative.py) | x² ≥ 0 over ℝ | `positivity`, `exact sq_nonneg x` |
| [examples/nat_add_zero.py](examples/nat_add_zero.py) | n + 0 = n over ℕ | `simp`, `omega` |
| [examples/implication.py](examples/implication.py) | P → P; a>0 ∧ b>0 ⇒ a+b>0 | `intro`/`exact`, `linarith` |
| [examples/bad_proof.py](examples/bad_proof.py) | false claim / wrong tactic | must be rejected |
| [examples/ai_batch.py](examples/ai_batch.py) | candidate proofs incl. LLM text | batch + JSON |

```bash
pyleanx show-lean examples/square_identity.py
pyleanx check examples/square_identity.py          # exit 0
pyleanx check examples/bad_proof.py                # exit 1, with diagnostics
pyleanx check examples/implication.py --json       # machine-readable
```

Scripts expose a module-level `THEOREMS` list or a `build()` function. **The CLI
executes the script as ordinary Python; only run scripts you trust.**

## Interactive proving (step by step)

```bash
pip install -e ".[interactive]"     # adds LeanInteract (pinned)
```

```python
s = thm.session()            # persistent Lean REPL; Mathlib loads once (~30 s here)
s.goals                      # ('x y : ℝ\n⊢ (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2',)
s.apply(pl.positivity())     # ❌ "not a positivity goal" — state unchanged
s.peek(pl.ring())            # try without recording
s.apply(pl.ring())           # ✔ no goals — each step takes well under a second once warm
s.undo()                     # step back
s.apply(pl.ring())
s.verify()                   # the ONLY way to get verified: batch Lean run + axiom audit
```

A session is an aid, like a Lean editor's goal view. `s.is_complete` only means the REPL
sees no goals; `s.verify()` turns the recorded tactics into a proof and runs the normal
batch check. Sessions share one REPL per project (`pl.shutdown_sessions()` stops it). In
Jupyter, sessions, goals and step results render as formatted output.

## Decorator syntax, Greek names, LaTeX

```python
@pl.theorem(proof=pl.positivity(), assumptions=lambda α, x: {"hα": α > 0})
def scaled_square(α: pl.Real, x: pl.Real):
    return α * x**2 + α > 0

scaled_square.verify()
scaled_square.to_latex()   # \forall \alpha, x \in \mathbb{R},\quad \alpha > 0 \;\Longrightarrow\; \alpha x^{2} + \alpha > 0
```

- `@pl.theorem` turns a function into a `pl.Theorem`. Parameter annotations give the sorts,
  and the function is called once with fresh symbols. It runs as ordinary Python; it is not
  a source-code compiler.
- Variable names may use Greek letters and subscript digits: `pl.symbol("θ", pl.Real)`,
  `pl.symbol("x₁", pl.Real)`. Python identifiers cannot contain `₁`; write `x1` there
  (it still displays as $x_1$). `λ`, `Π`, `Σ` are rejected because they are Lean syntax.
- `LeanProject(unicode_types=True)` / `--unicode-types` writes `ℝ ℕ ℤ ℚ` instead of
  `Real Nat Int Rat` (and imports the Mathlib notation modules).
- **Jupyter:** expressions render as typeset math, theorems as a typeset statement with
  the Lean source in a collapsible block, and results with ✅/❌. `pl.latex(obj)` returns
  the LaTeX string. LaTeX is display only; Lean only ever sees `to_lean()`.

## Algebra, analysis and plane geometry

```python
from pyleanx import algebra as alg, analysis as an, geometry as geo

alg.am_gm_two("am_gm", a, b)                         # 2ab ≤ a² + b², proof supplied
pl.Theorem("trig", [x], conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
           proof=pl.exact(an.sin_sq_add_cos_sq(x)))
A, B, C = geo.points("A B C")                        # points of ℝ²
pl.Theorem("angle_sum", [A, B, C], assumptions={"h": B != A},
           conclusion=geo.angle(A, B, C) + geo.angle(B, C, A) + geo.angle(C, A, B) == pl.pi(),
           proof=pl.exact(geo.angle_add_angle_add_angle_eq_pi(C, pl.hyp("h"))))
```

Each module's lemma catalog names declarations checked against the pinned Mathlib; see
[examples/domains.py](examples/domains.py) and the module docstrings for limitations.

## Seeing a Mathlib theorem as Lean states it

```python
pl.infoview(pl.algebra.two_mul_le_add_sq)      # or pl.infoview("name", imports=[...])
```
```
R : Type u
inst✝ : CommSemiring R
...
a b : R
⊢ 2 * a * b ≤ a ^ 2 + b ^ 2
```

This is Lean's own `#check` output laid out like the editor's infoview (no restating, no
proof). CLI: `python -m pyleanx infoview two_mul_le_add_sq --import Mathlib.Algebra.Order.Ring.Unbundled.Basic`.

## Theorem bank

`pl.TheoremBank` indexes declarations with the statements Lean reports, searches them
(`bank.search("triangle inequality")`), hands back version-checked lemma references
(`bank.ref(id)`), and stores your verified theorems with their evidence for reuse
(`bank.add_theorem`, `bank.load_with_dependencies`). CLI: `pyleanx bank index|search|show`.
See [examples/theorem_bank.py](examples/theorem_bank.py).

## Proof agents

`pyleanx.agent` lets programs and AI models propose proofs that Lean checks:
`agent.ProofEnv(thm)` (observe/act/undo/verify, plus JSON tool schemas for tool-calling
models), `agent.search_proof(thm, proposer)` (backtracking search; an LLM is just a
proposer), `agent.try_proofs` (no REPL needed), a 13-problem baseline benchmark
(`pyleanx agent bench`), and `pyleanx agent serve` (JSON lines over stdio). However a
script was found, it is **verified only by the batch Lean run and axiom audit**. See
[examples/agent_search.py](examples/agent_search.py).

## For AI and data pipelines

- `pl.verify_all(theorems)` checks many theorems in one Lean process, with a separate
  status, axiom audit and diagnostics for each.
- `VerificationResult.to_dict()/to_json()` and `pyleanx check --json` give a stable
  schema (`schema_version: 1`).
- `pl.raw_tactic("nlinarith [sq_nonneg (x - 1)]")` accepts model-generated tactic
  text, but it is **untrusted**: rejected unless the policy sets
  `allow_raw_tactics=True`, screened for commands/options, and still kernel-checked and
  audited. See [docs/security.md](docs/security.md).
- Diagnostics carry Lean positions, the tactic step that failed, and the Python line
  that created it.

## Notation caveats (read this)

- `==`, `<`, `<=`, … build **propositions**. Expressions have no truth value: `if x == 0:`,
  `and`, `or`, `not`, chained `0 <= x <= 1`, builtin `min`/`max` raise
  `SymbolicTruthValueError`. Use `pl.And/pl.Or/pl.Not` (or `&`, `|`, `~`),
  `pl.And(0 <= x, x <= 1)`, `pl.min/pl.max`.
- Expressions are unhashable (no dict keys/sets); compare with `a.same_structure(b)`.
- Python reflects comparisons with a literal on the left: `0 <= x` is rendered `x ≥ 0`
  (the same proposition in Lean).
- No Python floats: `0.1` is not exact. Use `pl.real("0.1")` or `pl.rat(1, 10)`.
  `2/3` is evaluated by Python *before* PyLeanX sees it; write `pl.rat(2, 3)`.
- No implicit coercions: `n + x` with `n : Nat`, `x : Real` is an error; write
  `pl.cast(n, pl.Real) + x`.
- `Nat` subtraction truncates and `/` on `Nat`/`Int` is floor division, exactly as in Lean.
- PyLeanX is not a general Python-to-Lean compiler; arbitrary Python functions are not
  translated.
- A kernel check certifies the **generated Lean statement**. Whether that statement
  faithfully captures the informal theorem you had in mind is your responsibility:
  always read `thm.to_lean()`.

## Documentation

The full documentation is at <https://vizpageai.github.io/pyleanx/>. In this repository:

- Tutorials: [first theorem](docs/tutorials/first-theorem.md),
  [using Mathlib](docs/tutorials/mathlib.md), [interactive proving](docs/tutorials/interactive.md),
  [checking derivations](docs/tutorials/scientists.md), [proof agents](docs/tutorials/ai.md)
- [docs/api.md](docs/api.md): API guide
- [docs/architecture.md](docs/architecture.md): design and trust pipeline
- [docs/security.md](docs/security.md): trust model, raw tactics, sandboxing
- [docs/troubleshooting.md](docs/troubleshooting.md)
- [docs/roadmap.md](docs/roadmap.md): milestones, test evidence, blockers
- [docs/stability.md](docs/stability.md): versioning and deprecation policy
- [IMPLEMENTATION_PLAN.md](IMPLEMENTATION_PLAN.md): the engineering specification

## Contributing, security, citing

Contributions are welcome: see [CONTRIBUTING.md](CONTRIBUTING.md) and the
[Code of Conduct](CODE_OF_CONDUCT.md). Report soundness problems privately as described in
[SECURITY.md](SECURITY.md). If you use PyLeanX in research, please cite it
([CITATION.cff](CITATION.cff)) together with Lean 4 and Mathlib.

## License

MIT. See [LICENSE](LICENSE). (Lean 4 and Mathlib are Apache-2.0; they are dependencies, not bundled.)

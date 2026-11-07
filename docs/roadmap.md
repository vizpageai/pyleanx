# Roadmap and status

Last updated: 2026-11-06 (first implementation session).

## Environment used for this session

| Item | Value |
|---|---|
| OS | Windows 11 Enterprise 10.0.26200 (x86_64) |
| Python | 3.13.14 (venv `.venv`) |
| elan / lake | elan-managed; Lake 5.0.0 |
| Pinned Lean | `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`) |
| Pinned Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` (`lean-project/lake-manifest.json`) |
| Mathlib cache | `lake exe cache get`: 8908 files downloaded+decompressed, 26 min 36 s, exit 0 |
| Git | the checkout is **not** a git repository, so no milestone commits were made |

Dependency sources (`.lake/packages`, 816 MB) were copied from an existing local
checkout pinned to the same Mathlib revision, to avoid re-cloning; `lake exe cache get`
then fetched prebuilt `.olean`s. No Mathlib source was rebuilt.

## Milestones

### M0: repository, pinned environment, baseline Lean proof: **done**
- [x] `pyproject.toml` (setuptools, Apache-2.0), README, LICENSE, `.gitignore`, CI workflow
- [x] `lean-project/` with `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`; same files shipped in the wheel (`pyleanx/_lean_template`)
- [x] `pyleanx doctor`
- [x] Direct Lean tests: square identity by `ring` passes with axiom report; wrong statement fails (`tests/integration/test_lean_basics.py::test_m0_*`)
- [ ] Linux CI run: workflow written (`.github/workflows/ci.yml`), **not executed** (no remote repo)

### M1: mathematical AST + operators: **done**
- [x] Sorts, `Var`, immutable `Expr` nodes, arithmetic, comparisons, typed literals, propositions, connectives, quantifiers
- [x] `__bool__` → `SymbolicTruthValueError`; unhashable; float/bool literals rejected; no implicit coercion (`pl.cast`)
- [x] Scope checks: undeclared variables, duplicate binders, capture/shadowing
- [x] Unit tests: `tests/unit/test_expr.py`, `test_types.py`, `test_scopes.py`

### M2: Lean code generation and proofs: **done**
- [x] `Theorem`, `Hypothesis`, tactic IR (ring, positivity, omega, simp, linarith, nlinarith, norm_num, intro, exact, apply, rw, use, rfl, decide, constructor, assumption, steps, branches, raw_tactic)
- [x] Deterministic renderer with precedence-aware parenthesisation, literal ascription, import resolver, source map with Python origins, identifier hygiene
- [x] Golden tests: `tests/unit/test_render.py`, `test_tactics.py`

### M3: real verification + audit: **done** (see test evidence)
- [x] Backend running the pinned `lean --json` with the project's Lake environment (resolved once, cached), process-tree kill on timeout
- [x] Position-attributed diagnostics and `#print axioms` audit; `AxiomPolicy`; fail-closed classification
- [x] Verified-only cache with full fingerprint; `--no-cache`
- [x] Integration tests: positive, negative, `sorry`, transitive `sorry`, foreign axiom, `native_decide`, spoofed audit, timeout, bad import, cache invalidation

### M4: CLI, docs, MVP: **done locally; CI not yet run**
- [x] `pyleanx init / doctor / show-lean / compile / check (--json) / cache stats|clear`
- [x] Examples: square identity, square nonnegative, `n + 0 = n`, `P → P` (+ linarith), bad proofs, AI batch
- [x] Docs: api, architecture, security, troubleshooting, this roadmap
- [x] Wheel + sdist build (`python -m build`)
- [ ] Linux CI and fresh-clone install test on another machine
- [ ] Jupyter: only `_repr_markdown_` on `Expr`/`Theorem` (no LaTeX rendering yet)

### Additions after the MVP (2026-11-06, session 2)
- [x] `@pl.theorem` decorator (execution-based: annotations give sorts; not an AST compiler)
- [x] Greek and subscript identifiers (`α`, `x₁`); `λ Π Σ` rejected
- [x] `unicode_types` / `--unicode-types`: `ℝ ℕ ℤ ℚ` with the Mathlib notation imports
- [x] LaTeX display: `to_latex()`, `pl.latex`, Jupyter `_repr_latex_` / `_repr_markdown_`
- [x] `python -m pyleanx` entry point (the `pyleanx.exe` launcher is blocked by policy on this machine)
- Evidence: `pytest tests/unit` 119 passed; real-Lean test
  `test_unicode_types_greek_names_and_decorator` passed (4/4 verified, 7 m 38 s).

### M5–M8: not started
- M5 LeanInteract backend (`backend/leaninteract.py`): not started. Must inspect the installed `lean-interact` API first.
- M6 domain modules, M7 theorem bank, M8 proof-agent API: not started.

## Test evidence (commands actually run)

| Command | Result |
|---|---|
| `lake exe cache get` (in `lean-project/`) | exit 0; 8908 files; 26 m 36 s |
| `ruff check .` | All checks passed |
| `pytest tests/unit -q` | **96 passed** (≈2 s) |
| `pytest tests/unit --cov=pyleanx` | IR + renderer modules ≈90 % line coverage (render 97 %, binders 97 %, types 100 %, expr 89 %, proofs 85 %) |
| `PYLEANX_REQUIRE_LEAN=1 pytest tests -q -s` (run 1, real Lean) | **125 passed, 6 failed** in 39 m 37 s |
| rerun of the 6 failures + perf after fixes | **6 passed, 1 failed** (`import Mathlib` mode: timeout at 900 s) |
| `python -m build` | wheel + sdist built; wheel contains `_lean_template/*` and LICENSE |
| `python -m pyleanx.cli doctor` | all checks passed, exit 0 |

Run-1 failures and their resolution:

1. `raw_tactic("positivity")`: the raw text carried no import, so the tactic was unknown. **Test fix**: pass `imports=[...]`. (Correct behaviour: it was *rejected*, not verified.)
2. `native_decide`: correctly `policy_rejected`, but Lean 4.34 names the axiom `native_two._native.native_decide.ax_*` rather than `Lean.ofReduceBool`. The policy already rejects `*_native*`; **test assertion updated**.
3. `abs_nonneg` test theorem collided with Mathlib's `abs_nonneg`; Lean rejected it ("already declared"). **Renamed**; documented in troubleshooting.
4. Three 300 s timeouts while a separate `lake build` was running on the same machine. Rerun with a 900 s test timeout: positivity and false-claim tests pass; only `import Mathlib` (all ~8900 modules) still times out. That test is now opt-in (`PYLEANX_SLOW_TESTS=1`). **Blocker on this machine, not a correctness failure**: the result was `timeout`, never `verified`.
5. Perf test measured an uncached call as "cached"; fixed.

Acceptance matrix (plan §8), all with real Lean unless noted:

| Case | Outcome |
|---|---|
| Algebra `ring` / Positivity / Nat `simp` / Logic `intro; exact` | verified |
| False claim `x^2 < 0` | rejected |
| Wrong tactic (`ring` on `x*y ≥ 0`) | rejected, error mapped to tactic step and Python line |
| Missing binder | `ScopeError` (unit) |
| `sorry`, transitive `sorry` via a cited lemma | policy_rejected (`sorryAx`) |
| Foreign `axiom bogus : False` | policy_rejected; accepted only with `extra_allowed={"bogus"}` |
| `native_decide` | policy_rejected by default; verified with `allow_native=True` |
| Spoofed audit text via `trace` | ignored; still policy_rejected |
| Raw tactic, default policy | policy_rejected without running Lean |
| Python truth value | `SymbolicTruthValueError` (unit) |
| Reproducibility | same fingerprint, cache hit (≈20 ms) |
| Policy / proof / Mathlib-rev change | new fingerprint, no cache hit |
| Timeout (0.05 s) | timeout, never verified |
| Bad identifier / injection | `IdentifierError` before rendering (unit) |
| Bad import module | environment_error |
| Batch `verify_all` good/bad/good | per-theorem verified/rejected/verified |
| CLI `check` valid / invalid | exit 0 / exit 1; `--json` schema v1 |

Measured timings on this machine (warm, with other Lean work running concurrently, so noisy):
direct `lake env lean` on the square-identity file 33.9 s; `thm.verify()` 32.5 s; cached
verify 20 ms; batch of 10 positivity theorems 220 s (unexpectedly high and not yet
explained; to investigate on an idle machine before claiming batch speedups).

## Known limitations / blockers

- **Lean import time on this machine is the bottleneck**: a direct `lake env lean` run of
  the square-identity file took ~44 s warm; the first cold run ~228 s. This is Lean
  loading Mathlib `.olean`s (likely slowed by on-access antivirus scanning on Windows),
  not PyLeanX overhead. Use `verify_all` to amortise one import load over many theorems.
- `lake env` costs ~10 s per call here; PyLeanX therefore resolves it once (`lake-env.json`).
  The first `lake env` in a fresh workspace took ~99 s (one-time Lake configuration).
- `import_mode="mathlib"` (`import Mathlib`) did not finish within 900 s on this machine;
  minimal imports (the default) are required here.
- Python reflects `0 <= x` to `x >= 0`; rendered statements are equivalent but not literally
  what was typed.
- Raw-tactic screening is heuristic; independent replay checking (`lean4checker`) is future work.
- No Linux CI evidence yet; no PyPI name check beyond the plan's note that `pylean` is taken.

## Next unfinished milestone

M4 release gates (Linux CI run, clean-machine install), then **M5** (LeanInteract backend).

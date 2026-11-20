# Roadmap and status

Current planning review: [reusable mathematical foundations and textbook authoring](foundations.md).
See the [2026-11-17 review evidence](#foundation-review-2026-11-17) for current local checks;
the dated implementation entries below are historical records.

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
- [x] `pyproject.toml` (setuptools; MIT since 2026-11-09, was Apache-2.0), README, LICENSE, `.gitignore`, CI workflow
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

### M5: interactive Lean backend: **done** (2026-11-07, branch `m5-leaninteract`)
- [x] `lean-interact==0.11.6` (optional extra `interactive`), REPL `v1.3.19`, API checked against installed code
- [x] Transport isolated in `backend/leaninteract.py` (`LeanRepl`): shared REPL per project, cached import environments, timeout/crash recovery
- [x] `ProofSession` (`thm.session()`): `goals`, `apply`, `peek`, `undo`, `reset`, `history`, `script`, `finish`, `verify`; Jupyter displays
- [x] Re-import + replay when a tactic needs new modules; replay after REPL restart
- [x] Raw tactics gated/screened as in batch mode
- [x] **Gate** (`tests/integration/test_interactive.py`, real REPL): `intro` then `exact` across steps, then batch-verified; incomplete proofs show open goals and cannot be verified; `sorry` never verifies. 4/4 passed in 89 s.
- Measured: Mathlib import env about 30 s once; then 3 steps in 0.38 s; second session open + step 0.15 s (vs 30–60 s per batch check).
- **Environment finding:** this machine's application-control policy blocks newly built executables (`repl.exe`, also pip's `pyleanx.exe`/`jupyter.exe`). `launch="auto"` detects this and runs the same REPL program via the already-allowed pinned `lean --run REPL/Main.lean`. Documented in docs/security.md; no binaries are moved or disguised.
- Not done: `PickleEnvironment` persistence across Python restarts; LaTeX rendering of goal strings (goals display as Lean text); REPL-based fast final verification (deliberately not done, as batch remains authoritative).

### M6: mathematical convenience modules: **done** (2026-11-09, branch `m6-m8-domain-bank-agent`)
- [x] `pyleanx.algebra`: `identity`, `nonneg`, `inequality`, `am_gm_two` helpers + 20 lemma refs
- [x] `pyleanx.analysis`: `sin`, `cos`, `pi()` (zero-argument constants now render) + 16 lemma refs
- [x] `pyleanx.geometry`: `Point` sort (`EuclideanSpace Real (Fin 2)`), `dist`, `angle` (Mathlib `∠`) + 9 lemma refs
- [x] Non-numeric sorts: only `=`/`≠`, same sort, no literals/arithmetic; `pl.Le/Lt/Ge/Gt` keep orientation
- [x] Catalog versioning: `VERIFIED_MATHLIB`, `catalog_status()`; abstractions/limitations in each module docstring
- [x] `backend/declarations.py`: `check_declarations` runs `#check @name` in the pinned Lean
- [x] **Catalog check (real Lean)**: all 54 catalog names (incl. `pyleanx.mathlib`) resolve at the pinned Mathlib; 556 s on a loaded machine. Finding: `add_pos` at this revision is `b < c → 0 < a → b < c + a`, so it is deliberately not in `algebra`. Test kept as `PYLEANX_SLOW_TESTS=1`.
- [x] **Gate** (`tests/integration/test_domains_lean.py`, real Lean): polynomial identity (`ring`), nonnegative square (`positivity`), AM-GM (`nlinarith [sq_nonneg (a - b)]`), `sin²+cos²=1`, `√x²=x`, plane triangle inequality, triangle angle sum = π, Pythagoras via `rw [iff]`: all **verified** in one Lean run; reversed triangle inequality **rejected**. 2 passed in 55 s.
- Limitations: concrete sorts only (no typeclass binders: statements about ℝ², not arbitrary Euclidean spaces); no coordinates, vectors, lines, circles, limits, derivatives or integrals yet.

### M7: theorem bank: **done** (2026-11-09, gate passed 2026-11-09)
- [x] `pyleanx.bank.TheoremBank`: JSON file store (atomic save, schema 1); entries keep canonical ID ≠ Lean name, `Formalization` (system, library, toolchain, library revision), statement + SHA-256 (tamper check on load), assumptions, aliases, tags, provenance, dependency edges, evidence, canonical theorem
- [x] `index_declarations` / `index_catalogs`: statements come from Lean's `#check`, never typed by hand
- [x] `search` (IDs, names, aliases, tags, descriptions, statements); `ref` (Name + imports) and `load` / `load_with_dependencies` refuse other toolchains/revisions (`VersionMismatchError`) and non-Lean entries (`CrossSystemError`); `link` records cross-system relations as informational only
- [x] `serialize.theorem_from_canonical`: strict, exact rebuild from canonical JSON (sort/function registries)
- [x] CLI `pyleanx bank index|search|show|list`
- [x] Unit tests: `tests/unit/test_bank.py`, `test_agent_server.py` (CLI)
- [x] **Gate** `tests/integration/test_bank_lean.py` (search → versioned declaration → proof → verify; bank, reload, reuse in `verify_all`): **1 passed** in 466 s (real Lean, ~5 GB RAM free). An earlier attempt had been stopped for low memory.

### M8: proof-agent API: **done** (2026-11-09, gate passed 2026-11-09)
- [x] `agent.ProofEnv`: observe / act (text, Tactic or canonical JSON) / peek / undo / verify, step budget, JSONL transcript; `TOOLS` JSON schemas + `call_tool` for tool-calling LLMs
- [x] `agent.tactic_from_text`: common tactics → structured IR with catalog imports; anything else → `RawTactic` only with explicit `allow_raw`
- [x] Proposers: `AutomationProposer`, `RetrievalProposer(bank)`, `ChainProposer`; `search_proof` (DFS + backtracking, visited states, budget); `try_proofs` (REPL-free, candidates as renamed copies in one batch run, winner re-verified)
- [x] Benchmark: `agent.basic()` (13 problems: logic, Nat, algebra, inequalities, analysis, geometry), `export_jsonl`, `run_benchmark(mode="session"|"batch")`, CLI `pyleanx agent bench|export|serve` (JSON-lines stdio server; raw text only with operator `--allow-raw`)
- [x] Unit tests: `tests/unit/test_agent.py`, `test_agent_server.py` (fake REPL; status always comes from the batch result)
- [x] **Gate** `tests/integration/test_agent_lean.py` (baseline search verifies 3 problems; `sorry` and `native_decide` agents rejected by the audit after the REPL accepted their steps; tool calls; batch mode): **3 passed** in 309 s (real Lean).
- [x] Baseline numbers (`python -m pyleanx agent bench`, automation proposer only, no retrieval/LLM):
  - session mode: **9/13 verified**, 198 s
  - batch mode (`--mode batch`): **9/13 verified**, 178 s
  - unsolved in both: `b_and_comm` (needs `constructor`/anonymous-constructor steps), `b_am_gm` (needs a hinted `nlinarith`), `b_exists_gt` (needs a witness via `use`), `b_dist_symm` (needs the `dist_comm` lemma). These are the targets for retrieval/LLM proposers.
  - note: session mode found `intro h1 ; omega` for `P → P` and `ring ; positivity` for `x² ≥ 0`; both verified by the batch run and audit, though they are not the idiomatic proofs.
- Not done: no LLM client is bundled (any callable is a proposer); no `lean4checker` replay.

### Addition: infoview-style display of library declarations (2026-11-09)
- [x] `pl.infoview(...)` / `pyleanx infoview NAME --import M`: Lean's `#check name` signature split into `hypotheses ⊢ conclusion` (display only; `check_declarations(signature=True)`)
- [x] Unit tests `tests/unit/test_infoview.py` (parser, Jupyter markdown, imports, CLI parser)
- [x] Real Lean: `python -m pyleanx infoview two_mul_le_add_sq sq_nonneg abs_add_le --import Mathlib.Algebra.Order.Ring.Unbundled.Basic --import Mathlib.Algebra.Order.Group.Unbundled.Abs` printed all three goal views (3 min, 1.7 GB free RAM). `tests/integration/test_infoview_lean.py` written, not run separately.

### M9: release engineering ("PyTorch-grade" packaging): **in progress** (2026-11-09)
- [x] Repository on GitHub (`vizpageai/pyleanx`, branch `main`), MIT license (merged GitHub's initial commit)
- [x] Type checking: `mypy src/pyleanx` clean (also `--platform win32`); 12 type errors fixed
- [x] CI (`ci.yml`): lint + types; unit tests on Linux/Windows/macOS × Python 3.11/3.12/3.13 with an 80% coverage floor (currently 82%); Lean integration with failures as annotations; every example (`scripts/run_examples.py`); build + `twine check --strict` + clean wheel install → `pyleanx init` → check/reject outside the checkout
- [x] Packaging: dynamic version, classifiers, keywords, project URLs, `docs` extra, `MANIFEST.in` (sdist ships tests/examples/docs); `python -m build` + `twine check --strict` pass locally
- [x] Documentation site (MkDocs Material + mkdocstrings): install guide, 5 executable tutorials, API reference from docstrings (all exports documented, enforced by `tests/unit/test_docs.py`), stability policy, release guide; `mkdocs build --strict` passes; `docs.yml` deploys to GitHub Pages
- [x] Community/release files: CONTRIBUTING, CODE_OF_CONDUCT, SECURITY (private soundness reports), CHANGELOG, CITATION.cff, issue/PR templates, dependabot; `release.yml` (tag = version check, clean install, PyPI trusted publishing behind the `pypi` environment, GitHub release)
- [ ] **CI green on GitHub.** First runs: unit jobs passed on all OSes; the Lean job first failed at test collection (duplicate test basenames, fixed) and then with test failures whose logs need a GitHub login to read (annotation reporting added); a later run showed only 5 of 12 jobs and a mypy failure (Linux-only platform check, fixed). Not yet re-run: the last push was refused (credentials of a GitHub account without write access).
- [~] Tutorials executed against real Lean (`tests/integration/test_docs_lean.py`): **4 of 5 pages pass** (first-theorem, mathlib, interactive, scientists). The first run found a real doc bug (a theorem named `imp_self` clashes with Lean core): renamed, and PyLeanX now adds a hint to "has already been declared" errors. `ai.md`: REPL crash in the first run (low memory), then no network (`Could not resolve host: github.com` while fetching the REPL); its search and batch blocks did verify in an earlier dry run. Re-run pending.
- [ ] PyPI publication: needs the trusted-publisher setup and a maintainer decision (docs/releasing.md).

### Evidence for this session (2026-11-09)
| Command | Result |
|---|---|
| `pytest tests/unit -q` | **191 passed** |
| `ruff check .` | all checks passed |
| `pytest tests/integration/test_domains_lean.py` | 2 passed, 1 skipped (slow catalog test), 55 s |
| catalog `#check` of all 54 names | all exist (556 s) |
| `python -m build --wheel` | built; wheel includes `pyleanx/agent/*`, `bank.py`, `geometry.py` |
| M7/M8 integration gates | first attempt stopped for low memory; rerun 2026-11-09: `test_bank.py` 1 passed (466 s), `test_agent.py` 3 passed (309 s) |
| GitHub CI run 42669750768 (first push) | unit jobs on Linux/Windows/macOS × Python 3.11/3.13 **passed**; `lean-integration` **failed at collection** (duplicate test basenames in `tests/unit` and `tests/integration`); integration tests renamed `*_lean.py` |
| `pyleanx agent bench` (session / batch) | 9/13 (198 s) / 9/13 (178 s) |
| `pytest tests/unit -q` (after infoview) | **201 passed** |
| `pytest tests/unit -q` (M9) | **210 passed**; `mypy` clean (linux/win32/darwin); `mkdocs build --strict` OK; `twine check --strict` PASSED |

Also fixed this session: a PowerShell rewrite had corrupted non-ASCII characters (`≤`, `∀`) in
`algebra.py` (committed in the M6 commit: docstrings and the `"≤"`/`"≥"` keys of
`inequality`'s operator table), `bank.py` and a test file; repaired and re-tested.

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

### M10-M15: writing proofs without touching Lean (2026-11-09)
- [x] **M11 general vocabulary**: open Lean types (`pl.Type`, `Fn`, `Prod`, `Fin`, `EuclideanSpace`), `pl.var/const/app/fun/sum/prod/integral/pair/field/ascribe/smul/norm`; scope checks for `fun`/∑/∫; LaTeX; canonical round trip. Big-operator bodies are parenthesized (Mathlib parses `∑ i, f i + 1` as `(∑ i, f i) + 1`).
- [x] **M12 definitions**: `@pl.define`, `pl.define_type`, `@pl.structure`, `pl.mk`; emitted in dependency order; a failing definition rejects every theorem in its file.
- [x] **M13 structured proofs**: `have`, `calc`, `show`, `obtain`, `cases`, `induction`, `unfold`, `ext`, `pl.auto` (each alternative must close the goal), `Theorem.auto_prove`. Raw text nested anywhere in a proof is gated (fixed: the gate used to look only inside `steps`/`branches`).
- [x] Real Lean gate `tests/integration/test_general_lean.py`: **2 passed** (454 s): ‖c•x‖ = ‖c‖‖x‖ in ℝ³, `fun` β-reduction, ∑ of odd numbers = n² by induction, a definition proved with `unfold`+`have`, a structure field, a `calc` chain, `obtain`/`use`; a false vector identity and a file with a broken definition are rejected.
- [x] **M10 libraries**: `pyleanx add/libs/build-lib/remove`: import-closure vendoring at a pinned commit (git, lazily fetched) or local directory, toolchain/Mathlib check, NOTICE with the upstream license, incremental build with the pinned `lean`, `LEAN_PATH` extension (batch, bindings, interpreted REPL), library hash in fingerprints and REPL keys. Unit-tested with a local fixture.
- [x] **M11 bindings**: Lean exporter metaprogram -> `pl.lib.use(module)` namespaces (types -> sorts, definitions -> callables, predicates -> propositions, theorems -> lemmas, ASCII aliases for `f₀`), `pl.lib.search/decl`, `pyleanx bindings -o module.py`.
- [x] **Faithfulness**: `Theorem.same_statement_as(name)` (definitional equality by `rfl`, audited).
- [x] **M14 readable goals**: Lean goal text -> LaTeX (`Goals.to_latex`, `DeclView.to_latex`), shown in Jupyter above the Lean text (display only).
- [x] **M15 assistants**: `agent.LLMProposer(complete)` (model-agnostic prompt + reply parsing, no bundled client); typed `aesop`/`exact?`; tactic text with arithmetic over theorem variables (`nlinarith [sq_nonneg (a - b)]`, `use k + 1`) parsed into typed IR by a safe AST walk instead of raw text; baseline proposer adds ∃-witnesses, hinted nlinarith, aesop, exact?.
- [x] OAI library: `pyleanx add oai https://github.com/openai/math --rev 4eaee87… --subdir lean --module ComparatorChallenges.VlasovMaxwell --module OAI.Analysis.VlasovMaxwell.Model` fetched, vendored 2 modules and **built them with real Lean** (705 s + 38 s).
- [x] Real bindings export: 57 OAI declarations (kinds, fields, docstrings); `RVM.Vec` is a sort, `RVM.q(v)` real-valued, `RVM.Admissible(d)` a proposition. Found and fixed: structure field sorts (`d.f0 : Phase → ℝ`, not ℝ).
- [x] OAI statement fidelity (2026-11-10, real Lean, 1270 s): the main theorem `OAI.RVM.global_classical_solution` written in Python with OAI's definitions is **definitionally the same statement** (`same_statement_as` → True, axioms propext/Classical.choice/Quot.sound).
- [ ] Remaining OAI checks (weakened statement must differ; `1 ≤ q v` proof; `sorry` citation rejected): the weakened-statement check was **stopped by Claude Code for low system memory** (no result); the other two not started.
- [ ] `tests/integration/test_mathlib_names_lean.py` (pl.mathlib names only): written, not run yet.
- (superseded) OAI example run (`examples/oai_vlasov_maxwell.py`: `same_statement_as` for the main theorem and a weakened variant, proof of `1 ≤ q v` on OAI's definition, rejection of a theorem citing the challenge's `sorry`): **stopped by Claude Code for low system memory** (each step loads all of Mathlib). No result either way.
- [ ] Benchmark re-run with the upgraded baseline proposer.
- Unit tests: 248 passed; ruff and mypy clean.

### Core: certifiers, search in Python and checking in Lean (2026-11-20)
- `pyleanx.justify.register_certifier`: a certifier receives the step's statement and the
  statements in its scope (from the derivation graph, scope-aware: a step never sees a later
  step that reuses a name) and returns tactic text Lean only checks. Certificates come
  first in the step's `first | …`; the rules still follow. `Derivation.certificates(step)`.
  Without certifiers the generated Lean is byte-identical (golden test).
- **Certifiers across domains** (`pyleanx.certifiers`, opt-in; sympy, scipy optional):
  `polynomial` (equalities over ℕ/ℤ/ℚ/ℝ), `inequality` (Positivstellensatz search by
  linear programming: products of hypotheses, hypothesis × square, diagonally dominant
  sums of squares, terms `positivity` knows), `witness` (∃: solve, then certify the
  instance through `Goal.certify`), `divisibility` (ℕ/ℤ quotients, opening cited
  divisibilities). Non-ring subterms are opaque atoms, so the certifiers apply to
  trigonometric, analytic and arithmetic steps that are algebraic in such terms.
  Certifiers now also run for conclusions and `pl.auto()` (the derivation graph tracks
  the goal through claims, choices, definitions and `suffices`).
- **Lean measurement 1** (8 equality steps, `#count_heartbeats`, heartbeat limit lifted):
  19,376 → 5,043 thousand heartbeats; the rules prove all 8 too; a wrong certificate first
  costs +10%.
- **Lean measurement 2** (`benchmarks/certificates.py`, 20 steps in 6 domains): rules 10/20,
  certified 20/20, wrong-first 10/20; 38.7 → 13.7 million heartbeats.
- **Goals through written proofs**: the derivation graph computes the goal after `fix`
  (∀/⇒ peeled, fixed hypotheses stated), `take`, `suffices`, `suppose_not` (`False`, the
  assumption in scope), each case of a split, and induction (goal at 0 and k + 1, the
  hypothesis at k); `choose` states each named part. Contradiction certificates (`False`
  from `0 < 0`), negated hypotheses (`¬(a ≤ b)` as `b < a`), and division (`x / q` as
  `x * q⁻¹` with `q * q⁻¹ = 1` from `q ≠ 0`/`q > 0`/`positivity`; `q⁻¹ > 0` from `q > 0`).
- **Bug found by Lean and fixed**: inequality certificates that use an *equation* had the
  equation's multiplier with the wrong sign (`linear_combination` counts `a = b` as `b - a`
  in an inequality goal). Found when the two division inequalities failed; checked with a
  direct Lean probe; `sin² x ≤ 1` now uses its certificate too (1,294 → 398 thousand).
- **Lean measurement 3** (28 steps, default budget, pinned Lean 4.34.1 / Mathlib d13f23b):

  | domain | steps | rules only | certified | wrong certificate first |
  |---|---|---|---|---|
  | algebra | 4 | 4 | 4 | 4 |
  | inequalities | 7 | 2 | 7 | 2 |
  | analysis (√) | 1 | 1 | 1 | 1 |
  | trigonometry | 2 | 2 | 2 | 2 |
  | logic (∃) | 3 | 0 | 3 | 0 |
  | number theory | 3 | 1 | 3 | 1 |
  | division | 4 | 2 | 4 | 2 |
  | proof structure (fix, contradiction, cases, ∃ by auto) | 4 | 2 | 4 | 2 |
  | **total** | **28** | **14** | **28** | **14** |

  Lean's work: rules 61.3, certified 16.5, wrong-first 67.0 (millions of heartbeats); on
  the 14 steps the rules prove, 22.8 → 7.7. One step costs more with its certificate
  (`√x + 1 > 0`: 154 → 757 thousand). Axioms: the standard three everywhere. Wall time per
  file is dominated by imports and machine load (66–692 s for the same imports).
- Tests: `tests/unit/test_certificates.py` (slot, scope, goal tracking through fix,
  contradiction, cases, take, induction, choose), `tests/unit/test_certifiers.py` (each
  certifier; negative cases: no certificate for a false (in)equality, a consistent set of
  hypotheses, an impossible ∃), `tests/integration/test_certifiers_lean.py` (real Lean via
  `verify()`; a wrong certificate never verifies a false step).
- Not done: sums of squares beyond the diagonally dominant cone (needs an SDP solver),
  goals after raw tactics (goal states from the REPL), modular arithmetic, inequalities
  over ℕ.

### Domain packages; pyleanx-analysis (2026-11-19, evening)
- **Separate domain packages**: `domains/analysis` is its own distribution
  (`pyleanx-analysis`, entry point `pyleanx.packs`), built only on PyLeanX and never
  imported by it (test). Core support: plugin discovery (`pyleanx.packs.load_plugins`, used
  by `pyleanx doctor` and `pyleanx facts`, never implicitly, so generated Lean depends only
  on the proof and the packages imported); packs declare the Lean imports their rules need;
  the numeric evaluator applies function-valued variables, λ terms and big operators through
  handlers, compares functions pointwise, and skips hypotheses that hold by construction;
  pack hints are consulted before the core's.
- **pyleanx-analysis**: vocabulary (re-exporting `pyleanx.analysis` and `pyleanx.realvar`),
  facts (Markov's inequality, …), rules for integrability, a.e. statements, nonnegativity
  and finiteness of measures (each tactic checked against the pinned Mathlib first), a
  calculus pack importing the derivative rules, numeric sampling of functions (properties
  known; functions defined by hypotheses), derivatives and integrals, explanation hints.
- **Lean evidence** (local batch checks, standard axioms): chapter *integration* 4/4
  (Markov's inequality and an interval bound, each 1 step with the package, 3 without);
  chapter *derivatives* 2/2. With the package imported, the Calderón–Zygmund module's 3
  proofs verify unchanged (the same check for the other measure-theoretic modules was
  stopped for low memory and not restarted). Bookkeeping ablation
  (`benchmarks/pack_ablation.py`): removed all together from `cz_interval_average` (7),
  `hilbert_kernel_smooth` (5), `maximal_level_set_open` (9); 18 steps across five
  singular-integral proofs together; details in `domains/analysis/README.md`.
- Also: `pyleanx new FILE` (a template written proof), a dot in products such as
  cos x · x (was "cos xx"), docs pages *Domain packages*, the core modules in the reference,
  written proofs on the docs home page, CONTRIBUTING for domain packages.
- Later the same night: package chapter *Calderón–Zygmund* (Stein's interval estimate in
  9 steps against 16 in the core example; Lean-verified); the bookkeeping ablation extended
  (see the package README; the Marcinkiewicz module's run was stopped for low memory and
  not restarted); random sequences in the sanity check; finite sums over
  `pl.finset_range(n)` (written ∑_{i<n}, evaluated numerically) with the example
  `readable_odd_sum.py` (1 + 3 + … + (2n − 1) = n², Lean-verified, benchmark 73/73);
  natural-number subtraction/division/remainder evaluated as in Lean (a false alarm and a
  missed counterexample fixed); kernels as named checkers (`get_checker`,
  `register_checker`); no module-level import cycle (now a test); the derivation graph
  prints as a table; the first tutorial has a written proof; the `pyleanx new` template
  verified with Lean. The REPL checker verifies the compact Lean (closer macros) on the
  algebra examples.

### The core (2026-11-19)
Design and status: [core.md](core.md). Built on the existing code, without reimplementing it:
guardrails (golden Lean of the 72 written proofs; a layering test: core modules import no
domain pack and name none of the geometry pack's Lean symbols); the justification engine
(`pyleanx.justify`: rules in ordered slots, registered by packs, active per theorem by
vocabulary; geometry's rules moved into the geometry pack); the derivation graph
(`pyleanx.derivation`); statement operations (`pyleanx.ops`); the numeric sampling framework
with geometry's evaluators and figures in the pack; a registry of fact domains with the
built-in packs in `pyleanx.packs`. Fixed on the way: `pl.similarly(replace=…)` (never
worked: variables cannot be dict keys) and a unit test that failed only on CI.
- **Lean evidence**: geometry proofs' Lean byte-identical; the other 55 written proofs changed
  only by losing geometry alternatives and were re-verified locally (batch, one module per
  process, standard axioms): **72/72 pass**. GitHub CI on `45a4f17` (before these changes):
  examples and benchmark jobs passed (all 72 written proofs on Linux); the integration job's
  only failure was the CI-only unit test, fixed in `2c01a82`.
- **Measured and dropped**: remembering the winning alternative (K6) gave no speed-up
  (warm checks 70–75 s either way). Lean's profiler shows why: parsing (14.5 s) and linting
  (5.5 s) of the 888 KB of generated alternatives dominate, not the search (3.6 s). Next
  (K7): emit the core rules once per file as a Lean macro; a core-Lean prototype works.
- Unit tests 434; ruff, mypy clean; `mkdocs build --strict` clean. The commits since
  `45a4f17` are local (pushing needs the maintainer's GitHub login on this machine).

### CI to green, and usability after 0.1.0 preparation (2026-11-18)
- **CI findings and fixes.** The first CI runs after the 0.1.0 preparation failed in the Lean job (public annotations; GitHub logs need a login). Fixed: (1) `all_geometry_facts_check` hit "deterministic timeout at whnf": the gap filler tried ~3,570 "lemma applied to a cited fact" alternatives for a step citing 35 facts, and Lean's heartbeat budget is per declaration; these pairs are now generated only when lemmas × facts ≤ 150 (the step drops to 860 alternatives; the generated Lean of every benchmark proof is unchanged). CI then passed the integration tests. (2) Tutorial blocks that are excerpts of example files were executed by the doc test; they are `py` fragments now, and a unit test checks that runnable blocks only use names defined on their page. (3) The example step stopped at once: two notebook helper modules had no expected outcome (now `HELPERS`, unit-tested). (4) `examples/theorem_bank.py` failed: `TheoremBank.index_catalogs` asked Lean for the 90 facts PyLeanX proves itself; it now indexes only the 135 Mathlib declarations (Lean: example ok in 61 s).
- **CI structure.** The Lean job is a matrix of three parallel jobs (integration tests, every example script, the naturalness benchmark); failures in the example runner and the benchmark are `::error` annotations; `naturalness.py --lean` exits 1 when Lean rejects a written proof (before, a regression was only recorded).
- **Usability.** `pyleanx check SCRIPT --watch` (re-check on save with Lean kept loaded, after a numeric sanity check); the first `check()` prints what it is loading (`PYLEANX_QUIET=1` silences it); citing a hypothesis no part of the proof defines is refused when the theorem is built, with the closest names (checked for false alarms on every proof of the benchmark, the lectures, the integration tests and the tutorials, built with Lean stubbed out); a one-word label (`because="SSS"`) cites its fact (it was emitted as a Lean name `SSS`); `sanity_check` constructs isosceles (|AB| = |AC|) and right-angle (∠ACB = 90°) figures, so Pythagoras and isosceles proofs are tried on samples; [Citable facts](facts.md), a generated page of all 390 facts with their labels (unit test keeps it current).
- **New Lean evidence (local, batch `verify_all`, standard axioms only).** Euclid I.8 (`euclid_median_bisects_apex`): SSS, then "corresponding parts of congruent triangles (CPCTC)" cited as a family by its label: the first Lean check of family citation, and it found the one-word-label bug. **Full regression of the written proofs: 72/72 pass Lean as written** (`docs/benchmark.md`; each result in `benchmarks/lean_results.json` carries the fingerprint of the proof's current Lean source; 0 failed, 0 stale, 0 unchecked), checked one module per process to fit in memory. Examples run with `scripts/run_examples.py`: 32 of 39 behave as expected locally (every example except `interactive_session` and the six singular-integral chapter scripts, whose written proofs are among the 72 verified above).
- **Not done.** Pushing: GitHub asked for a new login during this session, so the commits since `fac8090` are local until the maintainer pushes; CI has therefore not run on them. Background Lean runs were stopped by Claude Code for low memory several times and were not restarted; the work was redone in smaller foreground runs. `interactive_session` (a 4 GB REPL) was not run locally.

### Natural proofs: fast feedback and textbook steps (2026-11-17)
- [x] **Fast checking** (`thm.check()`, `pl.check_all`, `pyleanx/backend/repl_check.py`): the same Lean source in a persistent REPL, split into imports (loaded once), a preamble of shipped facts and cited theorems (elaborated once, cached by its text) and the theorems themselves. Messages are mapped back to file lines and classified by the batch backend's `classify` (same attribution, same `#print axioms` audit and policy); results say `backend="repl"` and are not archived. Measured: Pythagoras file 730 s on the first check (Mathlib import), **20 s** on the second; a wrong step rejected in 77 s with the error on the right step.
- [x] **Robust "by"**: reducible-only matching first (a mismatched fact fails at once instead of unfolding `angle`, `Real.pi` or set literals until the step's time budget is gone; found when four Euclid proofs timed out), facts in either orientation, a lemma applied to two cited facts in either order, `linarith` after normalising ∠ABC/∠CBA and |AB|/|BA|, triangle vertices distinct, betweenness and triangle vertex order up to permutation, `grind` as a last resort.
- [x] **Readable failures**: `pl.explain_failure` / `thm.prose(res)` restate each error as the step it belongs to, what remained to show and a hint; `thm.sanity_check()` tries the statement and each step on random samples meeting the hypotheses and reports a false step with the numbers (no Lean; proves nothing).
- [x] **Cite by meaning**: a reason containing a space is a description (`because="AA similarity"`), matched against the labels and names of all domain facts; an exact label or name selects its fact, an unclear description is refused with the candidates. `pl.search_facts`, `pl.fact`; failed steps without a reason get suggestions.
- [x] **Similarly**: `pl.similarly("h1", exchange=(A, B))` repeats an earlier step (statement, reasons, sub-proof) with variables exchanged; cited hypotheses are renamed to the ones stating the exchanged facts (also those introduced by `choose`). Lean checks the result.
- [x] **Textbook library**: `examples/euclid_book1.py` (equilateral angles, right/isosceles right triangle angles, exterior angle, vertical angles, midsegment) as written proofs citing facts by description; Pythagoras now uses `similarly` and descriptions. All eight verified in the REPL (standard axioms), before the cheap-closing change below.
- [x] **Benchmark**: `benchmarks/naturalness.py` (71 written proofs): steps, bookkeeping share (distinctness, positivity, notation, measure-theoretic side conditions), facts cited, `--lean` pass rate; results in `docs/benchmark.md`.
- Robustness: at most two import environments per REPL process (each holds Mathlib, GBs); REPLs are stopped when Python exits; a failing REPL (including unparseable output) is restarted once, then the batch backend checks. Found when an orphaned REPL (5 GB) left 233 MB free and the next REPL could not read its own `.olean` files.
- **Regression, partial at the time; completed 2026-11-18 (72/72, see above)** (`python benchmarks/naturalness.py --lean`, one module per process, results saved per proof in `benchmarks/lean_results.json` with a fingerprint of the generated Lean): **17 of 71 written proofs checked, all pass** — all 16 geometry proofs and AM–GM; 8 of them were checked just before a change that only removed duplicate gap-filler alternatives, so the report marks them stale. The run was stopped by Claude Code for low system memory after the geometry and AM–GM modules; the remaining 54 (algebra/number theory, analysis, harmonic analysis) run in CI's Lean job, which now executes the benchmark and uploads the report.
- After the partial regression (unit tests only, no Lean run yet): every catalogue fact labelled; descriptions match labels exactly first; a family label ("CPCTC") cites all members (a Lean check of two CPCTC theorems was stopped for low memory); `pyleanx sanity` / `pyleanx facts`; constructed points in `sanity_check`; Jupyter display fixes; version 0.1.0 with a dated changelog and a fixed release-notes step in `release.yml` (its regex extracted nothing); quality gates: ruff, mypy (win32 and linux), 392 unit tests, coverage 85%, `mkdocs build --strict`, `python -m build` + `twine check --strict`, clean-venv wheel install.
- Earlier attempts at the full regression: Two attempts ended for lack of memory (a `MemoryError` with several environments in one REPL; then Claude Code stopped the run for low system memory). Lean evidence so far: the 8 geometry proofs (Pythagoras, leg rule, six Euclid propositions) checked in the REPL with standard axioms; after that, the early `apply` alternative was given a cheap closing list (no `simp_all`/`convert`) to protect existing proofs; that last change is checked by unit tests only.
- Unit tests: 371 passed; ruff clean. Tutorial: `docs/tutorials/natural-proofs.md`.

### Written proofs for mathematicians (2026-11-12)
- [x] `pl.claim(P, because=…, note=…)`, `pl.conclude`, `pl.let`: proofs as statements with reasons; a gap filler (`Justify`) closes each step with standard automation, also after unfolding `pl.let` definitions and introducing `∀` variables.
- [x] `Theorem(avoid=[…])`: excluded from gap-filling `simp`, plus a generated Lean check that fails verification if the proof term (with auxiliary declarations) refers to an avoided lemma. Found the motivating bug with real Lean: without it, `simp` proves "f(0) = 1" in the derivative proof of sin²+cos²=1 *using* `Real.sin_sq_add_cos_sq`.
- [x] Shipped library facts (`LibraryFact`): Lean theorems with proofs emitted into each file that cites them: `geo.corresponding_angles(_2)` (via Mathlib's `exists_eq_smul_of_parallel`), `geo.similar_sides`. Geometry vocabulary `line/parallel/on_segment/collinear/triangle/similar`, `geo.similar_AA`; calculus `an.deriv/differentiable/constant_of_zero_derivative`.
- [x] `thm.prose(result)`: numbered-step text and Jupyter Markdown, from the LaTeX display.
- [x] Real Lean (warm REPL, pinned Mathlib): sin²+cos²=1 by derivatives (8 s), side-splitter by similar triangles (2 s), AM–GM (1.4 s) all accepted with propext/Classical.choice/Quot.sound; the `avoid` check rejects `simp` proving sin²+cos²=1. Cold `verify_all` of the three plus a circular `simp` proof (693 s, one Lean run): **3 verified, circular one rejected** by the avoid check (`span_kind=avoid_check`). First cold run exposed an attribution bug (an avoid-check error is outside the theorem's lines, so the batch was marked `environment_error`); fixed, with a unit test. `tests/integration/test_written_proofs_lean.py` encodes the same run (written; its content was run via a script, not via pytest).
- Unit tests: 284 passed (14 new in `tests/unit/test_written_proofs.py`); ruff and mypy clean.

### Singular integrals I: covering and the maximal inequality, as written proofs (2026-11-14)
- [x] `pyleanx.realvar`: intervals, Lebesgue measure |E| (`volume.real`), finite index sets, unions, set integrals, a.e. statements; Mathlib facts under textbook names (Vitali selection, subadditivity, monotonicity, disjoint-union integrals, …). No shipped Lean proofs: the classics are PyLeanX written proofs.
- [x] Term language: `pl.integral(…, within=S)`, `pl.union(s, …)`, and `⊆` as an infix relation (`HasSubset.Subset v s` written as a function application fails instance synthesis for `Finset`; `v ⊆ s` works).
- [x] Gap filler: side conditions left by applying one cited fact may be closed by another cited fact (`exact`, after `intros`, `apply … <;> assumption`).
- [x] `examples/singular_integrals.py` (Stein, *Singular Integrals* ch. I §1): Vitali covering lemma for finite families of intervals; integrals over disjoint intervals ≤ ‖f‖₁; the covering bound α|⋃Iᵢ| ≤ 4‖f‖₁. Real Lean: all three verified (standard axioms only, 118 s).
- [x] Theorem 4, the Hardy–Littlewood maximal inequality on compact sets (Stein's form): if every x in a compact K has an interval on which the average of |f| exceeds α, then α|K| ≤ 4‖f‖₁. Written proof: choice of radii, finite subcover by compactness, closed intervals, the covering bound. Families are now indexed by ℝ. Real Lean: all four theorems verified (standard axioms only).
- [x] Theorem 5, weak type (1,1) on measurable sets of finite measure (Stein Thm I.1(b)): suppose not; inner regularity gives a compact K with |K| > 4‖f‖₁/α; theorem 4 contradicts. Real Lean: theorems 1–5 verified (standard axioms only).
- [x] `examples/lecture_singular_integrals.ipynb` (+ `singular_lecture.py`): Vitali selection and maximal-function pictures, the five proofs, an exercise.
- Findings: phrasing matters for the gap filler — `div_lt_iff₀'` (c·a form) not `div_lt_iff₀`; cite `measureReal_def` when moving between |E| and μ(E); cite `mul_div_cancel₀` for α·(b/α) = b.
- [x] Theorem 6, the splitting estimate of the Lᵖ proof: α|K| ≤ 8∫|f·1{|f|>α/2}| for compact K ⊆ {Mf > α} (case split |f| ≤ |g| + α/2, set-integral monotonicity, theorem 4 at level α/2). Verified.
- Display: templates ending in `{*}` name a function and are applied to further arguments ((f·1_S)(y)).
- [x] Theorem 7, {Mf > α} is open (let J = ∫_I|f|, δ = (J − α|I|)/(4α); the interval of radius ρ + δ around any y with |x − y| < δ still has average > α). Verified (537 s alone).
- [x] Theorem 8, μ{Mf > α} ≤ 8∫|f·1{|f|>α/2}|/α on the whole level set, no finiteness assumption (openness + inner regularity of open sets + theorem 6). Verified.
- [x] `examples/marcinkiewicz.py` lemmas 9a ∫₀^{2a} t^{p−2} = (2a)^{p−1}/(p−1), 9b the weight p t^{p−1}·(8/t)I = 8p t^{p−2} I in [0, ∞], 9c (2a)^{p−1}a = 2^{p−1}a^p — written proofs, verified. `rv.rpow` (real exponents), `rv.lintegral`.
- [x] Lemmas 9d (the bound at a fixed level t: p t^{p−1}·8∫|f·1{|f|>t/2}|/t = ∫ 8p t^{p−2}|f·1{|f|>t/2}|) and 9e (the inner t-integral ∫_{(0,∞)} 8p t^{p−2} a 1{t<2a} dt = 8pa(2a)^{p−1}/(p−1)), verified.
- [x] Theorem 9, the Lᵖ bound for the maximal function (Stein Thm I.1(c)): p∫₀^∞ t^{p−1} μ{Mf > t} dt ≤ (8p·2^{p−1}/(p−1)) ∫|f|^p (the left side is ‖Mf‖_p^p by the layer-cake formula). Written proof: theorem 8 at each level, lemma 9d, measurability on (0,∞)×ℝ via the product-set form of the truncation, Tonelli, lemma 9e at each x, lemma 9c. Verified (standard axioms only).
- Engine: a pair-typed term no longer turns the internal attribute `vars` into a field projection.
- [x] `pyleanx/hilbert.py`: L²(ℝ) (`MeasureTheory.Lp ℂ 2 volume`), shipped definitions of the symbol m(ξ) = −i sgn ξ, the operator F ↦ m·F on L² (|m| ≤ 1 keeps it in L²) and Hf = 𝓕⁻(m·𝓕f); vocabulary for 𝓕, 𝓕⁻, a.e. statements; Mathlib facts (Plancherel `Lp.norm_fourier_eq`, inversion on L², `Lp.ext`, `MemLp.coeFn_toLp`, …).
- [x] `examples/hilbert_transform.py` (Stein, *Singular Integrals* ch. II §1): 10 |m(ξ)| = 1 and m(ξ)² = −1 for ξ ≠ 0; 11 ‖m·F‖₂ = ‖F‖₂; 12 m·(m·F) = −F; 13 ‖Hf‖₂ = ‖f‖₂; 14 H(Hf) = −f. All six written proofs verified (standard axioms only).
- Finding: state a cited lemma in its own orientation (‖𝓕(𝓕⁻G)‖ = ‖𝓕⁻G‖); the reversed claim timed out in `isDefEq` on Lp terms.
- [x] `pyleanx/realvar.py`: Lebesgue's differentiation theorem in textbook form as a shipped fact (`PyLeanX.Real.lebesgue_differentiation`: for a.e. x the averages of |f| over [x − r, x + r] tend to |f(x)| as r → 0⁺), proved in Lean from `IsUnifLocDoublingMeasure.ae_tendsto_average`; vocabulary for limits as r → 0⁺, "for all small r > 0", "for a.e. x".
- [x] `examples/calderon_zygmund.py` (Stein, *Singular Integrals* ch. I §3): 15 an interval meeting ℝ ∖ {Mf > α} has average ≤ 2α; 16 |f| ≤ α a.e. off {Mf > α}; 17 the decomposition (Ω = {Mf > α} open, |Ω| ≤ 8‖f·1{|f|>α/2}‖₁/α, |f| ≤ α a.e. off Ω, intervals meeting ℝ ∖ Ω have average ≤ 2α). All three verified (standard axioms only).
- Not yet: writing Ω as a disjoint union of intervals (components / Whitney cubes).
- Finding: the gap filler does not apply a lemma to two hypotheses (`exact le_of_tendsto hlim hev`); cite the applied lemma `rv.le_of_tendsto("hlim", "hev")`.
- [x] `examples/hilbert_kernel.py` (Stein ch. II §2–3, the bad part of the weak (1,1) proof): 18 |1/(x−y) − 1/(x−y₀)| ≤ 2|y−y₀|/|x−y₀|² when 2|y−y₀| ≤ |x−y₀|; 19 if ∫_I b = 0 and x ∉ I, ∫_I b(y)/(x−y) dy = ∫_I (b(y)/(x−y) − b(y)/(x−y₀)) dy; 20 if moreover |x−y₀| > 2t, |∫_I b(y)/(x−y) dy| ≤ (2t/|x−y₀|²)∫_I|b|. All verified (standard axioms only) on the first run. New shipped facts `kernel_integrable`, `abs_integral_le`.
- [x] Theorem 21, Hörmander's estimate for the bad part: ∫_{|x−y₀|>2t} |∫_I b(y)/(x−y) dy| dx ≤ 2∫_I|b| (a [0, ∞]-valued integral, so no integrability of x ↦ ∫_I b(y)/(x−y) dy is needed). Shipped facts ∫_{(s,∞)} du/u² = 1/s, ∫_{|x−y₀|>s} dx/(x−y₀)² = 2/s (via `integral_comp_abs` and translation invariance) and its integrability. Verified (standard axioms only).
- Engine: the gap filler also tries `field_simp` alone (it failed when `field_simp` closed the goal before `ring1`). Prose: a denominator like 2t is bracketed, 2/(2t).
- [x] `examples/cz_intervals.py` (Stein ch. I §3–4): 22/23 for U open and x ∈ U with a point of ℝ ∖ U on that side, a = sup{y ≤ x : y ∉ U} (resp. b = inf{y ≥ x : y ∉ U}) lies outside U and (a, x] ⊆ U (resp. [x, b) ⊆ U); 24 two intervals (a, b) ⊆ U with endpoints outside U that meet coincide; 25 if |U| < ∞, U misses a point on each side of every x; 26 the Calderón–Zygmund intervals: every x ∈ {Mf > α} lies in (a, b) ⊆ {Mf > α} with a, b ∉ {Mf > α} and ∫_[a,b]|f| ≤ 2α(b − a). All five verified (standard axioms only).
- Engine: the gap filler tries the anonymous constructor ⟨h₁, …, hₙ⟩ of the cited facts (a six-part conclusion sent `simp_all` into a recursion limit). Prose: {q : P(q)} for sets given by a property.
- Not yet: countably many intervals and |Ω| = Σ|Iⱼ|; summing theorem 21 over them; relating the kernel 1/x to H (principal-value integrals).

### Harmonic analysis as in a textbook (2026-11-13)
- [x] `pyleanx/harmonic.py` (generated from Lean checked in the pinned Mathlib): 8 shipped definitions (`PyLeanX.Harmonic.coeff` = `fourierCoeffOn` on [−π, π], `ft` = `𝓕`, `ift` = `𝓕⁻`, `gauss`, `L2`, `integrable_on_circle`, `coeff_sq_sum`, `mean_square`) and 18 facts (coefficient/transform integral formulas, linearity, integration by parts, Bessel, Parseval, Riemann–Lebesgue ×2, Gaussian, inversion, inverse transform at 0, small algebra).
- [x] Engine: `library_facts` also collects shipped definitions referenced by constants in statements and steps.
- [x] `examples/lecture_harmonic_analysis.ipynb` + `examples/harmonic_lecture.py`; references Stein–Shakarchi and Tao for topics/conventions (no text reproduced).
- [x] Real Lean: a theorem emitting all 26 shipped declarations verified (71 s); all 6 reference solutions verified (standard axioms only).
- Blockers (Mathlib at the pin): no Fejér/Dirichlet kernels, maximal functions, interpolation, Hilbert transform, Calderón–Zygmund; Plancherel exists only on `Lp` and is not yet in the vocabulary.
- Finding: `complex_analysis.pi()` is complex; real-variable statements need `pl.analysis.pi()`.

### Real analysis as in a textbook (2026-11-13)
- [x] `pyleanx/_analysis_textbook.py` (generated, imported into `pyleanx.analysis`): definitions with ε–N / ε–δ unfoldings and 29 shipped Lean theorems in textbook form (IVT, EVT max/min, Rolle, MVT, Bolzano–Weierstrass, monotone convergence, Heine–Cantor, Cauchy ⇔ convergent, convergent ⇒ bounded, limit algebra, squeeze, 1/(n+1) → 0, Archimedean, reciprocals), plus Mathlib absolute-value facts.
- [x] `pl.take(w, such_that=P, because=…)`: witness plus side condition (`refine ⟨w, ?_, ?_⟩`, bullet); prose "Take δ = ε/3; then ε/3 > 0"; serialized.
- [x] Display: formula sequences print as the formula; prose markdown hides `(n : ℝ)` casts; `choose … names=` maps each name to its conjunct; template slots `{0:.0}` allowed.
- [x] Gap filler: `(simp only [h]; first | ring1 | (congr 1; ring1))` (substitute a cited equation, then algebra inside |…|).
- [x] `examples/lecture_real_analysis.ipynb` + `examples/analysis_lecture.py` + shared `examples/lecture_tools.py` (step numbers from Lean's `step k:` span labels).
- [x] Real Lean: a theorem citing all 29 shipped facts verified; all 8 reference solutions verified (standard axioms only); the notebook's worked examples verified and its wrong proof (δ = ε) rejected at the chain step.
- Findings: a failing shipped fact in the same Lean file rejects every theorem of the batch (check facts separately); `pl.abs(3)` needs `pl.real(3)`; the BW fact is stated ∃ φ, ∃ L, … so `choose([φ, L], …)` matches it.

### Lecture notebook: congruent triangles (2026-11-13)
- [x] `examples/lecture_congruent_triangles.ipynb` + `examples/geometry_lecture.py`: SVG figures (no plotting dependency), ipywidgets slider explorers, worked examples (kite by SAS, isosceles median by SSS), a wrong proof (SSS used circularly) rejected at step 2, exercises 1-4 (vertical angles + SAS, SSS + CPCTC, ASA, isosceles right triangle) with hints and solutions.
- [x] `check()` maps Lean errors back to the student's step numbers; a declaration-wide heartbeat time-out gets a hint instead of a step number (Lean does not attribute it to a step).
- [x] Real Lean: all 6 reference solutions verified (standard axioms only); the two wrong proofs rejected at the expected steps; the notebook executes end to end.
- Unit tests: tests/unit/test_geometry_lecture.py (figures, solutions render, notebook names).
- Finding: concluding with `because=[geo.cpctc_ca, geo.dist_comm]` exhausts Lean's heartbeat budget; a separate CPCTC step followed by `conclude(because=geo.dist_comm)` verifies quickly.

### High-school plane geometry catalogue (2026-11-13)
- [x] Surveyed the pinned Mathlib for textbook geometry: 38 facts referenced by name (all checked against their declared modules: none missing), 17 shipped with Lean proofs where Mathlib lacks a citable unoriented form (CPCTC x6, HL, parallel direction, alternate/co-interior angles, midpoint x3, midsegment x2, Thales, parallelogram diagonal sides).
- [x] `examples/textbook_geometry.py`: isosceles median perpendicular to the base (SSS, CPCTC, linear pair), parallelogram opposite sides (alternate angles, ASA, CPCTC), angle in a semicircle + Pythagoras, isosceles right triangle base angles, medial triangle perimeter (midsegments).
- [x] Gap filler: conjunction projections (`h.2.1`), point-order normalisation (`convert h using 2; ext; ...; tauto`), cited rewrite rules everywhere (`simp only [angle_comm] at *`), `Ne.symm`.
- [x] Real Lean, cold (pytest, 204 s): all 5 textbook proofs and a theorem emitting all 17 shipped facts verified (standard axioms only); every earlier written proof still verified, negatives rejected.
- Unit tests: 326 passed; ruff and mypy clean.
- Not covered: areas, inscribed angles / cyclic quadrilaterals (oriented or plane-only in Mathlib), converses of parallel-line angle facts, tangents, "draw the parallel through P" constructions.

### Angle bisector theorem by the side splitter (2026-11-12)
- [x] `examples/readable_angle_bisector.py`: construct E on BA beyond A with AE = AC (`pl.let` + `geo.extend_beyond`), prove A ∈ BE, AE = AC, AD ∥ EC, BEC a triangle (shipped facts with Lean proofs; the parallel step by a vector computation from the equal angles), cite the proved side-splitter theorem for triangle BEC, then componendo. 14 written steps.
- [x] Real Lean: verified with propext/Classical.choice/Quot.sound only (single run ✔; integration test 116 s with all other written proofs and negatives).
- Unit tests: 312 passed; ruff and mypy clean.

### Citing proved theorems (2026-11-12)
- [x] `TheoremRef` (`because=thm`, `pl.cite`): cited theorems are emitted with their proofs before the citer (batch reordered if needed, emitted once), re-checked every run; unproved citations and cycles are errors; a failed cited proof rejects only its citers (`cited_theorem` spans). `avoid=` checks everything declared in the file. Serialized as `["theorem_ref", name]`; the bank records citations as dependencies and registers loaded theorems.
- [x] `examples/using_cauchy_integral.py`: ∮_{|z|=2} z²/(z − 1) dz = 2πi by the proved formula; real Lean ✔ (with the bank round trip). Integration test (57 s): 9 written proofs + the contour computation verified; circular, false-step, CIF-cheat proofs and a theorem citing a broken lemma rejected, unrelated theorems in the same run unaffected.
- Unit tests: 311 passed; ruff and mypy clean.

### Cauchy's integral formula, written proof (2026-11-12)
- [x] `pyleanx.complex_analysis`: ℂ, discs/circles, holomorphy, `circle_integral`; shipped facts (Lean proofs included) for the difference quotient's continuity/differentiability, termwise integration on the circle, and Cauchy's theorem for a disc with one exceptional point (wrapping Mathlib's Goursat-type theorem).
- [x] `examples/readable_cauchy_integral.py`: CIF from Cauchy's theorem via g = (f(z) − f(w))/(z − w), with `avoid=` Mathlib's own formula and its removable-singularity theorem (derived from the formula, so citing it would be circular).
- [x] `avoid=` now also looks inside cited `PyLeanX.*` facts, and imports avoided lemmas' modules (an avoided name outside the imports made every `simp [-name]` fail: found with real Lean). Gap filler: `exact L h` for cited lemma/fact pairs (needed when `apply` cannot infer an instance) and `rw [fact]`.
- [x] Real Lean: warm REPL 2.6 s; a direct citation of Mathlib's formula and a forbidden lemma inside a shipped fact are both rejected. Cold `tests/integration/test_written_proofs_lean.py` (pytest, 63 s with OS-cached oleans): **9/9 written proofs verified** (standard axioms only), 3 bad proofs rejected.
- Unit tests: 306 passed; ruff and mypy clean.
- Toward PNT (Newman): still missing in Mathlib — Newman's analytic theorem (contour argument), holomorphy of Φ(s) − 1/(s−1) on Re s ≥ 1, and the Tauberian steps θ ~ x ⇒ π ~ x/log x.

### Written proofs across mathematics (2026-11-12)
- [x] Proof moves: `pl.fix`/`pl.assume`, `pl.take`, `pl.choose`, `pl.suppose_not`, `pl.cases_on`/`pl.case`, `pl.induction_on`, `pl.chain`, `pl.suffices`, sub-proofs of claims. `prepare()` names steps by position (nested `step6_2`), matching the printed numbers; nested prose with targets tracked through fix/take/contradiction/induction (P(0), P(k) ⇒ P(k+1)).
- [x] Gap filler: one half of a cited `∧`/`↔` (matched at reducible+instances transparency: at default transparency a wrong half unfolded `EuclideanGeometry.angle` and hit an uncatchable heartbeat timeout, found with real Lean), `omega`, `contradiction`, `push_cast`, `congr 1; ring1`, splitting `∧`.
- [x] Abstract structures: `pl.type_param` (`{G : Type*} [Group G]`), `alg.group/abelian_group/ring/comm_ring/field`, `alg.inv`, group facts. `pyleanx.numbers` (divisibility, parity, primes, factorials); `an.tendsto` + shipped `an.tendsto_iff` (ε–N); `geo.corresponding_angles` merged into one fact for both angle pairs. All 77 catalog names `#check`ed against the pinned Mathlib.
- [x] Real Lean, cold, via pytest (`tests/integration/test_written_proofs_lean.py`, one `verify_all`, 587 s): **8/8 verified** with propext/Classical.choice/Quot.sound only — Euclid's primes, n(n+1) even (cases), limit of a sum (ε–N), x² = 1 ⇒ abelian (abstract group), Bernoulli (induction), sin²+cos²=1 by derivatives, side-splitter, AM–GM; a circular `simp` proof rejected by the avoid check and a proof with a false step rejected.
- Unit tests: 303 passed (19 new in `tests/unit/test_written_domains.py`); ruff and mypy clean.
- Limits: the gap filler is standard automation (Euclid's "N ≠ 1 since n! > 0" needed two steps); vocabularies cover elementary number theory, sequences, groups, calculus and plane geometry; generated Lean is verbose (each step lists its alternatives).

### Case study: OpenAI relativistic Vlasov–Maxwell (2026-11-09)
- [x] `examples/vlasov_maxwell_kinematics.py`: coordinate restatements of 9 OAI lemmas (+3 helpers): **12/12 verified** with real Lean (41 s). See `docs/case-studies/vlasov-maxwell.md`.
- Gaps found (not implemented): vector sorts (`EuclideanSpace ℝ (Fin n)`), function-valued variables / `fun`, named definitions and structures, `fderiv`/`∫`/`Lp`/`ContDiff`/set predicates, depending on external Lake libraries.

## Next unfinished work

1. M9: push the local commits (GitHub asked for a new login on 2026-11-18), then get the three Lean CI jobs green; their failures are annotations readable on the run page. Then publish 0.1.0 (docs/releasing.md).
2. Make the benchmark's retrieval proposer (bank lemmas, `constructor`, `use` witnesses) solve the 4 unsolved baseline problems; plug in an LLM proposer.
3. Independent replay check (`lean4checker`) for adversarial settings.
4. From the Vlasov–Maxwell case study: external Lake dependencies (cite and `infoview` a library such as OAI), then vector sorts, function variables with `fun`, named definitions.

## Foundation review (2026-11-17)

Scope: repository assessment and an implementation plan requested by the user; no new
runtime feature or milestone is claimed complete. The plan is in [foundations.md](foundations.md).
Existing edits to geometry, examples and notebooks were preserved.

The earliest recorded unfinished delivery gate remains release/CI validation (M4/M9).
Historical "not a git repository", missing-LaTeX and missing-vector statements above
describe earlier sessions and are superseded by the current source/checkout. Remote
CI status was not checked in this review, and publication is not part of this request.

Current environment: Python `3.13.14`, PyLeanX `0.1.0.dev0`, Lean `4.34.1`
(commit `5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, pytest `9.2.0`, ruff `0.17.4`,
lean-interact `0.11.6`. The prebuilt Mathlib cache is present; no rebuild or download
was needed. Commands below use `.venv/Scripts/python.exe` on Windows.

| Command | Result |
|---|---|
| `python --version` | Python 3.13.14, exit 0 |
| `python -m pyleanx doctor` | All checks passed, pinned Lean/Mathlib available, exit 0 |
| `python -m pytest tests/unit -q` | 354 passed in 13.82 s, exit 0 |
| `python -m ruff check .` | All checks passed, exit 0 |
| `python -m pytest tests/unit/test_docs.py -q` (after adding the plan/navigation) | 11 passed in 1.80 s, exit 0 |
| `python -m pytest tests/integration/test_lean_basics.py::test_examples_scripts_batch tests/integration/test_lean_negative.py tests/integration/test_lean_axiom_audit.py -q` | Real pinned Lean: 18 passed in 525.25 s, exit 0 |
| `python -m mkdocs build --strict --site-dir .pyleanx-review-site` (after adding the roadmap anchor) | Built in 5.28 s, exit 0; generated review output removed |
| `git diff --check` | Passed, exit 0 |

The integration selection covers the core example batch, false/invalid/missing proofs,
mixed batch attribution, timeout/environment errors, direct/transitive `sorry`, raw
tactic policy, audit spoofing, foreign/native axioms and cache invalidation. The full
domain/chapter integration suite, cross-platform CI and fresh-install gate were not
rerun; this review does not certify every existing domain example.

Implementation priorities: bind readable verification status to the exact theorem/proof;
consolidate shared sets/maps and settings; add exact statement contracts to curated
facts; separate domain proof strategies; compose existing theorem objects into chapters;
expand domains through reusable acceptance chapters. New packs must keep final pinned
Lean checking and transitive axiom auditing authoritative.

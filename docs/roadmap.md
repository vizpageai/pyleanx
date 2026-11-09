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
- [ ] OAI pilot (`examples/oai_vlasov_maxwell.py`): `pyleanx add oai …` vendored `ComparatorChallenges.VlasovMaxwell` and `OAI.Analysis.VlasovMaxwell.Model`; build and the example run are recorded below when finished.
- [ ] Benchmark re-run with the upgraded baseline proposer.
- Unit tests: 248 passed; ruff and mypy clean.

### Case study: OpenAI relativistic Vlasov–Maxwell (2026-11-09)
- [x] `examples/vlasov_maxwell_kinematics.py`: coordinate restatements of 9 OAI lemmas (+3 helpers): **12/12 verified** with real Lean (41 s). See `docs/case-studies/vlasov-maxwell.md`.
- Gaps found (not implemented): vector sorts (`EuclideanSpace ℝ (Fin n)`), function-valued variables / `fun`, named definitions and structures, `fderiv`/`∫`/`Lp`/`ContDiff`/set predicates, depending on external Lake libraries.

## Next unfinished work

1. M9: get CI green on GitHub (push access, then read the Lean job's failure annotations); run the tutorial gate; publish 0.1.0 (docs/releasing.md).
2. Make the benchmark's retrieval proposer (bank lemmas, `constructor`, `use` witnesses) solve the 4 unsolved baseline problems; plug in an LLM proposer.
3. Independent replay check (`lean4checker`) for adversarial settings.
4. From the Vlasov–Maxwell case study: external Lake dependencies (cite and `infoview` a library such as OAI), then vector sorts, function variables with `fun`, named definitions.

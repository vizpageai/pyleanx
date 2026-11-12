# Changelog

All notable changes are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and the project uses
[semantic versioning](https://semver.org/) (while in 0.x, minor versions may break the API;
see [docs/stability.md](docs/stability.md)).

## [Unreleased]

### Added
- Open Lean types: `pl.Type("…")`, `pl.Fn`, `pl.Prod`, `pl.Fin`, `pl.EuclideanSpace`;
  terms of these types are checked by Lean (built-in sorts keep their Python checks).
- General terms: `pl.var`, `pl.const`, `pl.app`, `pl.fun`, `pl.sum`, `pl.prod`, `pl.integral`,
  `pl.pair`, `pl.field`, `pl.ascribe`, `pl.smul`, `pl.norm`; structure fields as attributes.
- Definitions: `@pl.define`, `pl.define_type`, `@pl.structure`, `pl.mk`.
- Structured proofs: `pl.have`, `pl.calc`, `pl.show`, `pl.obtain`, `pl.cases`, `pl.induction`,
  `pl.unfold`, `pl.ext`, `pl.proof`, `pl.auto`; `Theorem.auto_prove`.
- External libraries: `pyleanx add/libs/build-lib/remove` (`pl.add_library`, …).
- Generated bindings: `pl.lib.use(module)`, `pl.lib.search`, `pyleanx bindings`.
- Faithfulness: `Theorem.same_statement_as(name)`.
- `pl.mathlib.<any Lean name>`: all Lean core, Batteries and Mathlib declarations by name, with
  the defining module found automatically (index of the pinned sources);
  `pl.mathlib.find/search`, `pyleanx mathlib find|search|index`.
- `pl.proof_graph(...)` / `pyleanx proof-graph NAME`: the lemmas, definitions and types a
  theorem rests on, as computed by Lean, down to its axioms, with statistics of the full
  dependency closure. Shown as a text tree, Mermaid (Jupyter), DOT, JSON or HTML.
- `pl.explain(...)` / `pyleanx explain NAME`: a library proof step by step: its exact
  source, the goal before and after each tactic and rewrite, the lemmas each step used, and
  their statements. Lean re-elaborates the pinned source. The result is marked `exact` only
  if the proof term and statement match the compiled ones Lean verified. It also accepts
  your own `pl.Theorem`; Lean then replays exactly the source `verify()` checks.
- Written proofs: `pl.claim(P, because=…, note=…)`, `pl.conclude(…)` and `pl.let(f, …)`
  write a proof as statements with reasons; Lean fills routine gaps with standard
  automation and checks every step. `thm.prose(result)` prints the proof as numbered
  steps (text or typeset in Jupyter).
- `Theorem(…, avoid=[lemmas])`: the proof must not use these lemmas. Gap-filling
  automation excludes them and a Lean check fails verification if the proof term refers to
  them (catches circular proofs, e.g. `simp` proving sin²+cos²=1 with that very lemma).
- Vocabulary for written proofs: `an.deriv`, `an.differentiable` and calculus facts;
  `geo.line`, `geo.parallel`, `geo.on_segment`, `geo.collinear`, `geo.triangle`,
  `geo.similar`, `geo.similar_AA`. Facts Mathlib lacks in citable form
  (`geo.corresponding_angles`, `geo.similar_sides`) ship as Lean theorems with proofs,
  checked in every file that cites them.
- Examples `readable_trig.py` (sin²+cos²=1 by derivatives), `readable_side_splitter.py`
  (similar triangles), `readable_am_gm.py`; `side_splitter.py`, `side_splitter_vectors.py`.

### Fixed
- Interactive sessions build and run the Lean REPL with the pinned toolchain's `lake`, so they
  work when elan has no default toolchain (as on CI) and never use a different Lean version.

### Changed
- The default time limit per Lean run is 900 s (was 300 s): a cold load of larger Mathlib
  modules (e.g. trigonometry) can exceed 300 s on a slow or memory-starved machine. The
  timeout diagnostic now says how to raise the limit.

### Security
- Raw tactic text nested inside structured proof steps is gated like top-level raw text.
- Lean type text is validated so it cannot escape its binder or add commands.
- A definition that fails to elaborate rejects every theorem in its Lean file.

## [0.1.0] - not yet released

First public release. Pinned to Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

### Added
- Typed, immutable expression IR with operator overloading (`pl.symbols`, `==`/`<=` build
  propositions, `pl.And/Or/Not/Implies/Iff/Forall/Exists`), exact literals, explicit casts.
- `pl.Theorem` and the `@pl.theorem` decorator; typed tactics (`ring`, `positivity`,
  `linarith`, `nlinarith`, `simp`, `omega`, `norm_num`, `intro`, `exact`, `apply`, `rw`, `use`,
  `constructor`, …) and gated `raw_tactic` for model-generated text.
- Deterministic Lean rendering with a source map; Python file:line origins in diagnostics.
- Batch verification (`verify`, `verify_all`) with a position-checked `#print axioms` audit,
  `AxiomPolicy` (rejects `sorryAx`, non-standard axioms and native evaluation by default),
  reproducibility fingerprint, verified-only result cache, stable JSON schema.
- CLI: `init`, `doctor`, `show-lean`, `compile`, `check`, `cache`, `bank`, `agent`, `infoview`.
- Interactive proof sessions on a persistent Lean REPL (`thm.session()`, `apply/peek/undo`).
- Jupyter display: typeset statements, results and goal states; `pl.latex`; Greek and
  subscript identifiers; `ℝ ℕ ℤ ℚ` output option.
- Domain modules `pl.algebra`, `pl.analysis` (sin, cos, π), `pl.geometry` (points of ℝ²,
  distance, angle) with lemma catalogs checked against the pinned Mathlib.
- `pl.TheoremBank`: Lean-indexed, versioned theorem bank with search and evidence.
- `pyleanx.agent`: `ProofEnv` with JSON tool schemas, proof search, proposers, a 13-problem
  benchmark (baseline 9/13) and a JSON-lines server.
- `pl.infoview`: Mathlib declarations displayed as Lean states them.

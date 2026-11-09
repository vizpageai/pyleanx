# Changelog

All notable changes are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and the project uses
[semantic versioning](https://semver.org/) (while in 0.x, minor versions may break the API;
see [docs/stability.md](docs/stability.md)).

## [Unreleased]

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

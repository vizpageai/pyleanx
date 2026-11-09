# Architecture

```
 Python user / AI agent
        │  pl.symbols, operators, pl.Theorem, tactics
        ▼
 ┌─────────────────────┐   expr.py, binders.py, proofs.py, theorem.py
 │ typed immutable IR   │   sort checks, scope checks, identifier hygiene
 └─────────┬───────────┘
           ▼
 ┌─────────────────────┐   render/lean.py, imports.py, render/sourcemap.py
 │ deterministic Lean   │   explicit imports, autoImplicit false,
 │ source + source map  │   `#print axioms` per theorem at a known line
 └─────────┬───────────┘
           ▼
 ┌─────────────────────┐   backend/subprocess_backend.py
 │ lake env lean --json │   pinned project (lean-toolchain + lake-manifest),
 │ (one process/batch)  │   timeout kills the process tree
 └─────────┬───────────┘
           ▼
 ┌─────────────────────┐   classify(): position-attributed errors and audit,
 │ audit + policy       │   backend/audit.py: AxiomPolicy
 └─────────┬───────────┘
           ▼
   VerificationResult  ──► backend/cache.py (verified results only)
```

## Principles

- **Own the representation, not the semantics.** Python does syntax construction and
  simple sort checks; Lean elaborates and checks everything. There is no Python
  type checker for dependent types.
- **Fail closed.** Any unexpected condition (missing or duplicated audit report,
  nonzero exit without an attributable error, import failure, timeout) yields a
  non-verified status.
- **Positions, not text.** Lean is run with `--json`; every message carries a
  position. Errors are attributed to theorems through the source map; the axiom
  report is accepted only if it sits on the `#print axioms` line PyLeanX generated for
  that theorem and names that theorem.
- **Determinism.** Rendering depends only on the IR (names, not object identities) and
  import settings. The fingerprint hashes the canonical IR, the exact Lean source,
  toolchain, Mathlib revision, manifest hash, policy, import mode, Lean options and
  backend version.

## Batch verification

`verify_all` renders all requested theorems into one file (one import load, which
dominates run time) and splits results by source-map spans. Theorems are emitted in
order, so a later theorem can cite an earlier one (`pl.ref(thm)`); if the earlier one
fails, Lean's error recovery adds it with `sorryAx`, so the dependent's audit fails too.

## Imports

`imports.py` collects modules from sorts (`Real` → `Mathlib.Basic.Real.Basic`), function
constants, tactics (`ring` → `Mathlib.Tactic.Ring`), lemma references, and explicit
theorem/project imports. `import_mode="mathlib"` emits `import Mathlib` instead.

## Layers added after the MVP

```
 agent/ (M8)  ProofEnv ─ proposers ─ search_proof / try_proofs ─ benchmark ─ server (stdio)
     │ uses                                   │ final check always via
     ▼                                        ▼
 session.py + backend/leaninteract.py (M5)   verify_all (batch + audit)
     ▲                                        ▲
 bank.py (M7): TheoremBank ── backend/declarations.py (#check @name) ── serialize.py
     ▲
 algebra.py / analysis.py / geometry.py (M6): sorts, Funcs, lemma catalogs (_domain.py)
```

- **Sessions (M5)** give goal states from a persistent REPL. They feed a recorded script
  to the batch backend and never decide verification themselves.
- **Domain modules (M6)** add sorts (`geometry.Point`), typed function constants
  (`Real.sin`, `dist`, `EuclideanGeometry.angle`) and lemma catalogs (`Name` + imports),
  versioned by `_domain.VERIFIED_MATHLIB`.
- **Bank (M7)**: entries store canonical ID ≠ Lean name, formalization (toolchain,
  library revision), statement + SHA-256, and evidence. `serialize.theorem_from_canonical`
  rebuilds PyLeanX theorems exactly from JSON (sort and function registries:
  `types.register_sort`, `serialize.register_func`).
- **Agents (M8)**: tactic text → IR (`agent/parse.py`; anything unstructured is a gated
  `RawTactic`); `ProofEnv` wraps a session and keeps a transcript; search and benchmarks
  report `verified` only from batch results.

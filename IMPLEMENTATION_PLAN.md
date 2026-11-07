# PyLeanX: Python-native frontend for Lean 4
## Codex engineering specification — v1.1 (2026-11-06)

### Changes in v1.1 (review of v1.0)

- **Audience made explicit:** two first-class users — human mathematicians *and* AI agents / ML pipelines. Added the PyTorch analogy (§0.1) and AI-facing MVP hooks (§2.1): machine-readable results, batch verification, gated untrusted tactic text.
- **Concrete pins (§1):** Lean `v4.34.1` + Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, chosen because a populated Mathlib cache for this pair already exists on the development machine.
- **Audit hardening (§5.1):** diagnostics are read from `lean --json` with source positions; the `#print axioms` result is accepted only when it is attributed to the exact line PyLeanX emitted for that theorem, so printed text inside a proof cannot spoof an audit. Proof text may not change kernel-relevant options (`set_option`, `debug.*`).
- **Semantics clarified (§4):** no implicit numeric coercions (explicit `pl.cast`), literal typing rule, `!=` builds `≠`, truncated `Nat` subtraction/division are Lean semantics and documented, not "fixed".
- **Import paths verified against the pinned Mathlib:** `Mathlib.Data.Real.Basic` is a deprecated alias at this revision; `Real` maps to `Mathlib.Basic.Real.Basic`.
- Removed the confusing `h = pl.symbol("h", pl.Prop)` line from the `Nat` example; fixed the git-commit rule for non-repo checkouts.

## 0. Mission and scope

Build an open-source Python package provisionally named `pyleanx` that lets a mathematician construct symbolic mathematical expressions, declare theorems, request proof tactics, view generated Lean code, and verify results using **Lean 4's kernel**. The developer experience should resemble PyTorch's Python-first API, while mathematical correctness remains dependent on Lean 4 rather than Python calculations or an LLM.

### 0.1 The PyTorch analogy (what "a PyTorch for Lean" means here)

| PyTorch | PyLeanX | Note |
|---|---|---|
| `torch.Tensor` + operator overloading | `pl.Expr` + operator overloading | builds a graph/IR, never evaluates math in Python |
| dtype (`float32`, `int64`) | sort (`pl.Real`, `pl.Nat`, ...) | no silent dtype promotion; explicit `pl.cast` |
| autograd graph | immutable typed theorem/proof IR | deterministic, fingerprinted |
| `torch.compile` / TorchScript export | `thm.to_lean()` | pure, deterministic codegen |
| CUDA/CPU backend | Lean 4 elaborator + kernel | the *only* source of truth |
| `nn.Module` libraries | `pyleanx.algebra`, `pyleanx.analysis`, ... (M6) | thin wrappers over Mathlib |
| batched training loop | `pl.verify_all([...])`, JSON results | the loop an AI prover runs |

The analogy is about *ergonomics*, not trust: PyTorch computes; PyLeanX only describes, and Lean decides.

This is a **new Python frontend**, NOT a Lean implementation in Python, NOT a general-purpose Python-to-Lean compiler, and NOT just a subprocess wrapper. A public package named `pylean` already exists; do not attempt to publish under that name. `pyleanx` is a provisional import and CLI name, subject to name/availability checks before release.

### Product invariant

`result.verified` is true ONLY after a Lean toolchain pinned by the project has accepted the exact generated theorem and its proof, the declared theorem statement was generated from the intended Python AST, and a proof-dependency axiom audit has passed the configured policy. Never use a text-only LLM response, a symbolic calculator, successful Python execution, zero remaining REPL goals, or process exit code alone as proof of verified correctness.

### In scope for MVP (M0-M4)

- Python 3.11+ library using public mathematical objects.
- Symbolic `Nat`, `Int`, `Rat`, and `Real` types, named variables, literal constants, arithmetic, comparison, equality, logic, quantifiers, and local hypotheses.
- Typed immutable intermediate representation (IR), deterministic Lean 4 code emission, safe naming, explicit source locations.
- Tactic combinators `simp`, `ring`, `omega`, `positivity`, `intro`, `exact`, `apply`, `rw`/`rewrite`, plus finite proof sequences. Do not promise every tactic works for every goal.
- One-shot theorem generation using a pinned Lean 4/Mathlib project, with explicit and inspectable imports.
- Verification result with statuses, diagnostic messages, generated Lean source, timings, axiom dependencies, and reproducibility fingerprint.
- CLI, tests, developer documentation, runnable examples.

### Explicitly out of scope for MVP

- Full dependent type theory implemented on the Python side; arbitrary Lean metaprogramming or typeclasses; arbitrary Python functions compiled to Lean; a general PDE proof automation engine; autoformalization of natural language; theorem discovery AI; a Mathlib mirror or universal Lean-to-Python decompiler; cloud execution; untrusted-code execution as a hosted service; an MTBank production server.

### Guiding principle

Own Python *representation*, not all Lean *semantics*. Python does syntax construction and simple type checks. Lean elaborates and verifies the authoritative statement and proof.

---

## 1. Reference technology and version policy

- Python `>=3.11`; use `pyproject.toml` and `uv` or standard `pip`; pytest, ruff, mypy/pyright optional.
- Lean 4 and `elan`/`lake`; start with an official Mathlib project generated via `lake new <project> math` or the official documented toolchain-specific equivalent.
- **Pinned for v0.1:** `leanprover/lean4:v4.34.1`, Mathlib rev `d13f23b723b8a846827a245b89c10fc7d3f11612` (transitive deps in `lean-project/lake-manifest.json`). The same three files ship inside the wheel as a template so `pyleanx init` can recreate the workspace outside a source checkout.
- Pin `lean-toolchain` and commit `lake-manifest.json`. Verify their consistency.
- Run `lake exe cache get` during initial setup; DO NOT rebuild all Mathlib sources unnecessarily.
- Backend #1: `subprocess.run(["lake", "env", "lean", <generated-file>], cwd=<pinned_project>, ...)` with explicit timeout, resource limits where available, controlled working directory, and captured stdout/stderr. *(v1.1: `lake env` itself costs ~10 s per call on the dev machine, so the environment it sets — `LEAN`, `LEAN_PATH`, `LEAN_SYSROOT`, … — is resolved once per pin configuration, cached keyed by a hash of the three pin files, and the pinned `lean` binary is executed directly with it. `resolve_env_once=False` restores the per-call `lake env lean`.)*
- Backend #2 (M5): LeanInteract (`lean-interact`) with `LeanREPLConfig`, `LeanServer`, `LocalProject`, `Command`, and `ProofStep` APIs verified against a pinned dependency version. The upstream API may change; make a transport adapter and integration tests rather than hard-coding assumptions throughout the package.
- Use Python AST (`ast`) only if/when adding an optional source-syntax frontend. The MVP operates as a normal Python **library**; user code is executed as normal Python, which is not a security sandbox.

References:
- https://lean-lang.org/install/manual/
- https://github.com/leanprover-community/mathlib4
- https://github.com/augustepoiroux/LeanInteract
- https://lean-lang.org/doc/reference/latest/ValidatingProofs/
- https://pypi.org/project/pylean/

---

## 2. Required developer experience

The following is a **target API** for implementation, not currently executable:

```python
import pyleanx as pl

x, y = pl.symbols("x y", pl.Real)

thm = pl.Theorem(
    name="square_identity",
    variables=[x, y],
    conclusion=(x + y)**2 == x**2 + 2*x*y + y**2,
)
thm.prove(pl.ring())
result = thm.verify()
assert result.verified, result.diagnostics
print(thm.to_lean())
print(result.axioms)
```

Expected generated Lean (import choices can be adjusted after integration testing):

```lean
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem square_identity (x y : Real) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

#print axioms square_identity
```

Note: In Lean's syntax `Real` may be an alias for `\u211d`; prefer canonical Lean identifiers and adapt to the selected Mathlib toolchain. Test all emitted syntax in the real backend.

Second example with an explicit hypothesis:

```python
n = pl.symbol("n", pl.Nat)
identity = pl.Theorem(
    "nat_add_zero",
    variables=[n],
    conclusion=n + 0 == n,
)
identity.prove(pl.simp())
assert identity.verify().verified
```

Another supported pattern:

```python
P = pl.prop_symbol("P")
lemma = pl.Theorem("identity_imp", variables=[P], conclusion=pl.Implies(P, P))
lemma.prove(pl.steps(pl.intro("h"), pl.exact("h")))
assert lemma.verify().verified
```

Python-like decorative syntax such as `with proof():` is not an MVP requirement. Normal Python `and`, `or`, and `not` DO NOT support symbolic logical operands; provide `pl.And`, `pl.Or`, `pl.Not` or overloaded `&`, `|`, `~` and document the caveat. Chained comparisons (e.g. `0 <= x <= 1`) do not work symbolically; use `pl.And(0 <= x, x <= 1)`.

### API contracts

- `pl.symbol(name, sort)` -> fresh `Var` with stable binder identifier; `pl.symbols("x y", sort)` -> tuple.
- `pl.Real`, `pl.Nat`, `pl.Int`, `pl.Rat`, `pl.Prop` -> type descriptors (not numeric Python types).
- `pl.Eq(lhs, rhs)` and overloaded `lhs == rhs` -> proposition IR. Since `__eq__` returns a symbolic Expr, do not use symbolic objects as dictionary keys or in Python truth tests. Implement `Expr.__bool__` to raise a precise `SymbolicTruthValueError`. Implement structural comparison separately: `expr.same_structure(other)`.
- Make Expr dataclasses `eq=False`, immutable/frozen (or equivalent), and avoid Python equality/hashing of Expr for internal map/set semantics.
- `pl.Forall([x], body)` and `pl.Exists([x], body)` explicitly bind variables, with capture-safe binder IDs and scope validation.
- `pl.Theorem(name, variables, assumptions=..., conclusion=...)` accepts only proposition-valued conclusion and hypotheses. Assumptions should be named and ordered (e.g., list of `Hypothesis(name, proposition)` or insertion-ordered mapping) for deterministic Lean proof context.
- `thm.prove(tactic_or_steps)` sets a proof AST, not an already-verified result.
- `thm.to_lean()` returns deterministic Lean source and should be pure, without invoking Lean or changing globals.
- `thm.verify(project=...)` always verifies the **current** proof AST and returns a `VerificationResult` object.
- `VerificationResult` fields: `verified: bool`, `status` (`verified`, `rejected`, `timeout`, `environment_error`, `policy_rejected`), `diagnostics`, `axioms`, `lean_source`, `toolchain`, `mathlib_revision`, `source_map`, `duration_ms`, `cache_hit`, `fingerprint`.
- `project` defines Lean toolchain, Mathlib revision, imports, trusted axiom policy, and timeout; no invisible dependence on a mutable global import state.

### 2.1 AI-facing contracts (in MVP scope)

AI provers and data pipelines are first-class users. The MVP therefore includes, without weakening the trust model:

- `VerificationResult.to_dict()` / `.to_json()` with a stable schema, and `pyleanx check --json`.
- `pl.verify_all(theorems, project=...)`: verify many theorems in **one** Lean process (one import load), attributing every diagnostic and axiom report to its theorem by source position. Each theorem still gets its own audit and status.
- `pl.raw_tactic(text)`: opaque tactic text (as an LLM would produce). It is **untrusted input**: rejected with `policy_rejected` unless the policy sets `allow_raw_tactics=True`; even then it is screened (no commands, `set_option`, `#`-commands, declarations, `unsafe`/`extern`/`implemented_by`, or dedent out of the `by` block), and the result records `raw_tactics_used=True`. Kernel check + position-attributed axiom audit remain authoritative.
- Diagnostics carry Lean positions and the PyLeanX source-map entry (theorem / hypothesis / tactic step) plus Python file:line origin where known, so an agent can localize failures.
- Interactive goal states (`.goals`) come with the M5 LeanInteract backend; proof search APIs remain M8.

---

## 3. Source-code structure

```text
pyleanx/
  pyproject.toml
  README.md
  LICENSE
  AGENTS.md
  src/pyleanx/
    __init__.py
    errors.py
    types.py                # Type descriptors and type compatibility rules
    expr.py                 # Immutable expression IR and operators
    binders.py              # Variables and quantifier scoping
    theorem.py              # Theorem declaration and lifecycle
    proofs.py               # Proof and tactic IR
    imports.py              # Lean import dependency mapping
    render/
      __init__.py
      lean.py               # AST -> Lean syntax with identifier escaping
      sourcemap.py          # Generated line/column -> source object
    backend/
      __init__.py
      interface.py          # VerifyBackend interface
      subprocess_backend.py # lake env lean one-shot backend
      audit.py              # #print axioms policy and parsers
      cache.py              # Cache keys and local SQLite/file cache
      leaninteract.py       # Phase 5, optional interactive backend
    cli.py                  # pyleanx init/doctor/compile/check/show-lean
    notebook.py             # Phase 6, optional rich repr
    mathlib.py              # Named theorem/tactic mapping
  lean-project/
    lean-toolchain
    lakefile.toml           # generated against pinned Mathlib; do not hand-guess
    lake-manifest.json
  tests/
    unit/
      test_expr.py
      test_types.py
      test_scopes.py
      test_render.py
      test_tactics.py
      test_policy.py
    integration/
      test_lean_basics.py
      test_lean_negative.py
      test_lean_axiom_audit.py
      test_cli.py
      test_performance.py
  examples/
    square_identity.py
    square_nonnegative.py
    nat_add_zero.py
    implication.py
    bad_proof.py
  docs/
    api.md
    architecture.md
    security.md
    troubleshooting.md
    roadmap.md
```

Use thin modules and interfaces; avoid a monolithic Python parser and avoid large auto-generated code in version control.

---

## 4. Typed IR, parsing, semantics, and rendering

### 4.1 Sort and type model

Define `TypeExpr` and minimal primitive types: `Nat`, `Int`, `Rat`, `Real`, `Prop`. Optional future types: `Type(level)`, `Set(T)`, `Fin(n)`, `List(T)`, `Vector(T,n)`, `Function(A,B)`, `EuclideanSpace(d)`. Define explicit type compatibility and numeric literal coercion rules. Do NOT silently permit arbitrary coercions that may change mathematical meaning.

### 4.2 Expression nodes

Frozen or immutable nodes with distinct IDs and source spans where feasible:

- `Var(id, user_name, type)` and `BoundVar(id, name, type)`
- `NatLiteral`, `IntLiteral`, `RatLiteral` (avoid accidental Python float semantics)
- `App`, `Const`, `Add`, `Sub`, `Mul`, `Div`, `Pow`, `Neg`
- `Eq`, `LE`, `LT`, `GE`, `GT`, `Not`, `And`, `Or`, `Implies`, `Iff`
- `Forall`, `Exists`, `Lambda` (Lambda optional for MVP)
- `LeanRef(qualified_name, known_type?)` for library declarations

Represent rational literals via exact `fractions.Fraction`; do not accept a binary Python float as exact Real by default. Provide `pl.real("0.1")` if useful. Integer literals can be coerced by expected type (e.g. `x+2` for Real x).

Typing rules (v1.1):
- Python `int` literals take the sort of the typed operand they meet; a literal with no typed context must be built with `pl.nat/pl.integer/pl.rat/pl.real`, otherwise a Python error is raised. Python `bool` and `float` are rejected.
- Operands of different sorts are an error; `pl.cast(e, sort)` performs the explicit, semantically safe embeddings Nat→Int→Rat→Real and renders as `(↑(e) : Real)`.
- Exponents in `**` must be `Nat` (Lean `Monoid.npow`).
- Unary minus on `Nat` is rejected. Truncated `Nat` subtraction and floor division on `Nat`/`Int` follow Lean semantics and are documented, not silently changed.
- `!=` builds `≠`. `Eq` between propositions is rejected in favour of `pl.Iff`.

### 4.3 Operators and Python pitfalls

- Overload arithmetic and comparison operations to build expressions (not evaluate them).
- `Expr.__eq__` returns a proposition, but internal structural equality must not use `==` or Python dict hashing. Implement `same_structure()` and stable canonical IDs.
- `Expr.__bool__` raises `SymbolicTruthValueError` with message suggesting `pl.And`/`pl.Or` or explicit Lean proof.
- `and`, `or`, `not`, Python `if`, set membership, `sum` over symbolic generators, Python chained comparisons, and math functions are NOT transparently symbolic. Document alternatives; do not claim compatibility before implementation.
- Avoid eager Python division for constants when it could change natural-number semantics: `2 / 3` evaluates to float BEFORE an API sees it. Provide `pl.rat(2,3)` for exact fractions.
- Treat mathematical `P` in `Forall(P : Prop, ...)` as a proposition variable rather than a Bool.

### 4.4 Rendering and name hygiene

- Deterministic whitespace, safe parentheses, valid Lean identifiers, and explicitly resolved imports.
- Identifier escaping/sanitization: no string injection. Disallow newlines, punctuation, qualified paths, and reserved keywords in user-defined declaration names unless handled through a documented safe quoting mechanism.
- Keep separate code paths for a trusted typed `LeanRef` and user-supplied strings. Every emitted tactic is constructed from a recognized tactic node, not raw arbitrary text. Extension hooks must be opt-in and clearly marked as unsafe / untrusted.
- Track generated source spans for error-to-Python diagnostic mapping.
- Explicitly close over bound variables; reject missing binders and name captures before emission.
- Keep displayed notation separate from internal Lean names; this allows future readable views.

### 4.5 Proof IR

Define typed nodes `Simp(lemmas=...)`, `Ring`, `Omega`, `Positivity`, `Intro(names)`, `Exact(ref_or_hyp)`, `Apply(ref)`, `Rewrite(ref, direction)`, `Steps([...])`, optional `Cases` and `Induction` later. Require imports mapped to tactics. Render `by` blocks, not arbitrary text templates.

---

## 5. Backend, trust, and reproducibility

### 5.1 Batch backend

1. Validate theorem IR with Python-side structural checks.
2. Resolve minimal necessary Lean imports from tactic and symbol mappings.
3. Generate a `.lean` source file in an isolated per-task build directory inside a pinned Lake project; record line-level source mappings.
4. Include `set_option autoImplicit false`; emit exact declaration and proof; append `#print axioms <fully-qualified-name>`.
5. Invoke `lake env lean --json <generated-lean-file>` with safe argument arrays, no shell string interpolation, explicit cwd, timeout (killing the whole process tree), captured output, and error classification.
6. Parse the JSON messages (severity, position, text); do not accept type errors or missing definitions. Any error inside a theorem's source-map span rejects that theorem; import errors are `environment_error`.
6a. Accept an axiom report only if it is an `information` message positioned exactly at the `#print axioms` line PyLeanX emitted for that theorem and names that theorem. Text printed elsewhere (e.g. by a raw tactic) is ignored, which prevents audit spoofing. A missing attributed report means `policy_rejected`.
7. Audit the printed transitive axiom dependencies; permit by default only Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`; reject `sorryAx`, custom axioms, and `_native` trust extensions unless configured to explicitly allow them with prominently surfaced provenance.
8. Only return `verified=True` if compilation succeeds AND audit succeeds. Any missing or unparseable audit output must be `policy_rejected` or `environment_error`, not verified.
9. Report the exact Lean/Mathlib commit, proof source, dependencies, timing, and fingerprint.

Lean's own proof validation documentation explains why compile success alone is insufficient and how `#print axioms` reveals proof dependencies: https://lean-lang.org/doc/reference/latest/ValidatingProofs/ . Source token screening for `sorry` is NOT enough, since transitive dependencies can hide it.

Threat note: the `#print axioms` audit assumes the generated file itself is not adversarial. Typed tactics guarantee that; raw (AI-produced) tactics are screened but screening is a heuristic. For adversarial settings (public leaderboards, hosted service) add an M5+ step that replays the produced `.olean` through an independent checker such as `lean4checker`/`comparator` as described on the Lean "Validating Proofs" page.

For higher robustness in later phases, replace fragile text parsing with a small version-pinned Lean helper emitting structured JSON axiom/declaration data using the Lean APIs; keep compiler exit code and kernel checking authoritative. Test the audit on multiple pinned versions.

### 5.2 Caching

Cache only verified results, never silently reuse a proof after its source or environment changes. Hash: canonical theorem IR + proof IR + imports + generated Lean + Lean toolchain + Mathlib commit + backend version + trusted-axiom policy + relevant Lean options. Keep cache local (e.g. SQLite metadata and files). Add `--no-cache` verification mode for audits. Distinguish cached verification provenance clearly.

### 5.3 Runtime safety

- Python API execution is ordinary Python execution and is NOT sandboxed. A hosted remote service must later isolate untrusted Python code and Lean processes using OS containers, quotas, timeouts, restricted network, and filesystem access.
- Avoid shell=True, never interpolate untrusted theorem text into shell commands, validate path boundaries.
- Bound memory, CPU, process count, and compile time in shared or cloud environments.
- For local MVP, document that the execution environment is trusted developer code and that the generated Lean code is compile-checked.

---

## 6. CLI and workflow

Commands:

```text
pyleanx init [directory]       # generate or validate a pinned Lean/Mathlib project
pyleanx doctor                 # Python, elan, lake, Lean, manifest, Mathlib cache status
pyleanx show-lean <script.py>  # run trusted local Python script, print generated Lean
pyleanx compile <script.py>    # emit Lean file(s), no claim of verification
pyleanx check <script.py>      # run verification; nonzero exit on rejection (--json, --no-cache, --timeout)
pyleanx cache stats
pyleanx cache clear
```

MVP script interface: a module-level explicit list named `THEOREMS` or `def build(): return [thm]` to determine what CLI checks. Do not indiscriminately inspect arbitrary module objects. Since scripts execute when imported, make the trust model explicit and offer a later non-executing AST mode.

`pyleanx doctor` should detect missing Lean, mismatched toolchain, missing Mathlib cache, and provide actionable corrections. Use `lake exe cache get` for Mathlib cache setup and avoid repeated source recompilation.

---

## 7. Incremental milestones for Codex

### M0: Repository, exact environment, and baseline Lean proof
Deliver: packaging, license, README, pin tooling, Lake Mathlib project and successful baseline Lean tests. Implement `pyleanx doctor`. Use the official Mathlib template and cached artifacts. Pin exact versions and record in a lockfile/manifest. Tests: a direct Lean square-identity `ring` theorem succeeds, a wrong statement fails, axiom report is available. CI can run a compact Linux smoke target.

**Gate:** Fresh checkout + documented setup + direct Lean verification pass; no blanket rebuild of Mathlib needed on ordinary runs.

### M1: Mathematical AST + Python operators
Deliver: `TypeExpr`, `Var`, immutable `Expr`, arithmetic, comparisons, typed constants, propositions, `And`/`Not`/`Implies`, simple binders, and structural fingerprint. Unit tests for expression construction, scoping, name collision, types, float and boolean pitfalls.

**Gate:** No Lean integration needed; at least 90% unit coverage of IR/renderer semantics; tests demonstrate symbolic-equality and truth-value behavior.

### M2: Lean code generation and proofs
Deliver: `Theorem`, `Hypothesis`, tactic AST, deterministic renderer, import resolver, source map, and safe identifiers. Golden tests for several statements and proofs; generate readable `.lean` files.

**Gate:** Existing golden cases produce stable, valid Lean code and reject unsupported constructs explicitly.

### M3: Real verification and proof-policy audit
Deliver: `SubprocessLeanBackend`, actual `lake env lean` invocation, diagnostics, timeouts, `#print axioms` audit, `VerificationResult`, safe cache. Integration tests for positive and negative proof cases and deliberate `sorry`/custom-axiom cases.

**Gate:** Positive tests return verified; false or incomplete theorems never do; `verified` is never inferred from a mock or empty-goals report.

### M4: CLI, documentation, stable MVP
Deliver: `pyleanx init/doctor/show-lean/compile/check`, five working examples, docs, versioned wheel, Linux CI, benchmark comparison versus direct Lean. Jupyter rendering may be a minimal `_repr_latex_` addition if low effort.

**Gate:** New Python user can install, run 4 example theorems, inspect generated Lean, and receive useful failures without writing Lean manually.

### M5: Interactive Lean backend
Deliver: `LeanInteractBackend` using a pinned `lean-interact` release; incremental proof steps, `.goals`, `.apply()`, `goals`/environment state tracking, restarts, response decoding, sessions, and timeout recovery. Batch final verification is always required before marking any proof verified. Keep REPL transport behind an interface.

**Gate:** A user can apply `intro` then `exact` across successive interactive steps and verify the final complete theorem with the batch backend; incomplete proofs show open goals and remain unverified.

### M6: Mathematical convenience modules
Deliver: `pyleanx.algebra`, `pyleanx.analysis`, `pyleanx.geometry` as thin, versioned wrappers around Mathlib concepts. Start with basic algebra and Euclidean plane triangles, rather than automatically reproducing the fully general 4-universe AA similarity theorem. Record exact abstractions and limitations. Add more advanced Lean typeclass and binder support only when tested.

**Gate:** End-to-end examples prove a polynomial identity, a nonnegative square, and a simple geometry proposition by reusing pinned Mathlib facts.

### M7: Mathematical Theorem Bank adapter (optional future)
Deliver: local theorem search index first; external MTB client later. Store canonical theorem ID separate from Lean fully qualified name; maintain exact formalization version, theorem statement hash, assumptions, aliases, provenance, dependency edges, and verification evidence. A theorem ID does not by itself certify equivalence across libraries/systems.

**Gate:** Search -> return exact versioned declaration -> apply in proof -> kernel-check result; unsupported cross-system equivalence never silently assumed.

### M8: AI integrations (future)
Deliver: proof-agent API to query hypotheses/goals, propose tactics, and attempt proofs through Lean. AI suggestions never become `verified` without the same batch checking and axiom audit. Add benchmark datasets and retrieval baselines.

---

## 8. Exact acceptance-test matrix

| Case | Input / setup | Expected |
|---|---|---|
| Algebra | `(x+y)**2 == x**2+2*x*y+y**2`, `ring` | verified |
| Positivity | `x**2 >= 0`, `positivity` | verified |
| Nat | `n+0 == n`, `simp` | verified |
| Logic | `P -> P`, `intro h; exact h` | verified |
| False mathematical claim | `x**2 < 0` universally over Real | rejected |
| Wrong tactic | `ring` on unrelated proposition | rejected |
| Missing type/binder | undeclared variable in statement | explicit Python error |
| `sorry` dependency | proof uses `sorry`, or uses a lemma that does | policy_rejected |
| Foreign axiom dependency | lemma depends on `axiom bogus : False` | policy_rejected |
| Native computation trust | axiom involving `_native` is detected | policy_rejected by default |
| Python truth value | `if x == 0:` where x symbolic | SymbolicTruthValueError |
| Reproducibility | same inputs/versions with warm cache | same fingerprint, cache hit |
| Version change | change Mathlib commit or axiom policy | cache invalidates |
| Timeout | artificially low timeout | timeout, never verified |
| Bad identifier | injection or illegal theorem name | reject before Lean rendering |
| Source mapping | forced Lean error | Python origin identified where possible |
| CLI | check valid/invalid example | 0/nonzero exit code respectively |
| Batch | `verify_all` with one good and one bad theorem | per-theorem statuses verified/rejected |
| Audit spoofing | raw tactic prints a fake "does not depend on any axioms" line | not accepted as audit; sorry still policy_rejected |
| Raw tactic gate | `raw_tactic` with default policy | policy_rejected before Lean runs |
| Implicit coercion | `n + x` with `n : Nat`, `x : Real` | explicit Python error; `pl.cast` works |

Do not use tests that simply assert a mock backend's success. Golden-unit tests are necessary but not sufficient; retain true Lean integration tests as release gates.

---

## 9. Performance requirements

- Establish measurements for cold toolchain setup, warm `lake env lean` with small imports, proof checking time, per-theorem repeated verification, and concurrent task memory consumption.
- Prefer narrow imports (`Mathlib.Tactic.Ring`, `Mathlib.Tactic.Positivity`, etc.) rather than blanket `import Mathlib` when possible.
- Cache Mathlib `.olean` files with `lake exe cache get` at provision/setup time.
- Cache verification by content + versions; reuse a pinned project rather than create a new one for every call.
- Avoid spawning many simultaneous Lean processes on RAM-constrained machines; cap concurrency.
- Distinguish first-run installation/build time from steady-state theorem check time; publish actual timings, not promises of x-fold acceleration.
- For M5, benchmark persistent LeanInteract sessions against batch compilation, with crash isolation and fallbacks.

---

## 10. Quality gates and release policy

- Python package installs from a clean virtual environment.
- `ruff check .`, `pytest tests/unit`, and real `pytest tests/integration` (with Lean present) pass.
- `python -m build` creates a distributable wheel/sdist with no credential data.
- Linux CI always runs full proof verification; macOS/Windows may start as smoke tests if resource availability is limited.
- All included examples execute successfully in the pinned environment.
- Any 'verified' status must include a reproducibility fingerprint and a clean axiom report.
- README contains a clear notation/semantics warning: symbolic `==`, `and`/`or`/`not`, chained comparisons, float handling, no general Python compilation.
- License is specified clearly; dependencies and third-party licenses recorded.
- Documentation explains that trusted kernel checks depend on correctly representing the intended informal theorem.

---

## 11. Instructions for the Codex coding agent

1. Work phase by phase, starting at M0. Inspect the repository first; preserve existing user work if the repo is nonempty. Do not delete or overwrite unrelated files.
2. Before coding an integration, inspect actual installed package APIs and upstream docs. Prefer supported public interfaces; do not invent classes or arguments.
3. Produce small, reviewable commits at each milestone when the checkout is a git repository (do not `git init` a user's directory unasked). Prefer tests first for parser/IR/axiom policy.
4. After each phase: run the appropriate checks; report exact commands, their real exit status, files changed, any broken assumptions, and the next phase. Do not label a milestone complete if a required integration test was not executed successfully.
5. Do not claim proofs checked without running Lean. Do not use `sorry` or `admit` to make acceptance tests pass. Deliberately failing test fixtures may use `sorry`, with documented expected policy rejection.
6. Keep batch verification the source of truth; LeanInteract is an interactive aid, not a replacement for the final proof audit.
7. Use file-based plan tracking, for example `docs/roadmap.md`, checkboxes and test evidence. If environment is missing Lean or external downloads fail, implement and test offline portions, report the blocker explicitly, and leave the integration gate unfinished rather than pretending it passed.
8. Provide concise runnable examples and an honest implementation status table at the end of each session.

## 12. First Codex session: required output

At the end of the first session, expect:
- `pyproject.toml`, working `src/pyleanx/` package, and smoke CLI.
- A pinned Lean/Mathlib project with cache setup instructions and verified direct Lean examples if Lean is available.
- First IR types/expressions and unit tests (if progress allows).
- `docs/roadmap.md` with M0 status and exact working/not-yet-working features.
- A log of commands actually run, including toolchain versions and test output summaries.
- No claims of a completed Python-to-Lean compiler before M2/M3 gates are really met.

## 13. Long-term extensions (after a proven MVP)

- VS Code and Jupyter experience: rendered mathematical syntax, code origin tracebacks, hover type inspection, tactic suggestions.
- An optional Python-source compiler using `ast.parse`, supporting `@theorem` decorated definitions through a tightly specified static subset, without executing arbitrary code for parsing. *(v1.1: an execution-based `@pl.theorem` decorator, LaTeX display, Greek/subscript identifiers and an `ℝ ℕ ℤ ℚ` output option already exist; the non-executing AST mode is still future work.)*
- Lean to readable-Python *view* using LeanInteract declaration metadata, with explicit warnings where typeclass arguments/implicit binders are hidden. This is not guaranteed to round-trip arbitrary Lean.
- Advanced geometry abstracted from Lean's typeclass structures; generalize Euclidean-plane wrappers only with type-safe tested translations.
- PDE module: Sobolev spaces, integrals, regularity assumptions, PDE models, estimates, and verified reusable lemmas. PDE proof automation is a separate research project.
- MTB versioned theorem IDs, semantic search, dependence graph, reproducible formalization snapshots, and AI agents.

## 14. Definition of MVP success

A completely fresh user can clone the repository, run documented setup, define at least four verified example theorems using Python objects, inspect the generated Lean, receive usable errors for failing examples, and demonstrate that `sorry`/foreign axioms cannot be silently labeled verified. Only then advertise an MVP as a reliable mathematical proof frontend.

# PyLeanX API reference (v0.1)

All names are available as `import pyleanx as pl`.

## Sorts

`pl.Nat`, `pl.Int`, `pl.Rat`, `pl.Real`, `pl.Prop` are descriptors of Lean types
(`Nat`, `Int`, `Rat`, `Real`, `Prop`), not Python numeric types.

## Symbols and literals

| Call | Result |
|---|---|
| `pl.symbol("x", pl.Real)` | fresh variable `x : Real` |
| `pl.symbols("x y", pl.Real)` | tuple of fresh variables |
| `pl.prop_symbol("P")` | proposition variable `P : Prop` |
| `pl.nat(3)`, `pl.integer(-3)` | typed integer literals |
| `pl.real("0.1")`, `pl.real(2)` | exact real literal (`1/10`, `2`) |
| `pl.rat(2, 3, sort=None)` | exact fraction; untyped unless `sort` is given |
| `pl.cast(e, pl.Real)` | explicit embedding Nat → Int → Rat → Real, rendered `(↑e : Real)` |
| `pl.TRUE`, `pl.FALSE` | `True`, `False` |

Each variable has an identity (`uid`). Two variables with the same name are different
variables, and using both in one theorem is a `ScopeError`.

Python `int` literals take the sort of the term they combine with (`x + 2` with
`x : Real`). Python `float` and `bool` are rejected.

## Expressions

Arithmetic: `+ - * /`, `**` (natural-number exponents only), unary `-` (not on Nat),
`//` and `%` (Nat/Int only). Functions: `pl.sqrt`, `pl.exp`, `pl.log` (Real),
`abs(e)`/`pl.abs`, `pl.min`, `pl.max`. Custom typed functions use
`pl.Func("Lean.name", (arg sorts…), result_sort, imports=(…))`.

Propositions: `==`, `!=`, `<`, `<=`, `>`, `>=`; `pl.Eq`, `pl.Ne`, and `pl.Le`, `pl.Lt`,
`pl.Ge`, `pl.Gt`, which keep the written orientation (Python turns `0 <= x` into
`x >= 0`, which matters when a hypothesis must match a Mathlib lemma such as
`Real.sq_sqrt : 0 ≤ x → …`);
`pl.Not(p)`/`~p`, `pl.And(p, q, …)`/`p & q`, `pl.Or(…)`/`p | q`,
`pl.Implies(p, q, …)` (right-nested), `pl.Iff(p, q)`,
`pl.Forall([x, y], body)`, `pl.Exists([x], body)`.

Structural API: `e.same_structure(other)`, `e.canonical()`, `e.to_lean()`,
`pl.free_vars(e)`.

## Theorems

```python
pl.Theorem(name, variables=[...], assumptions=..., conclusion=prop,
           imports=(...), proof=None)
```

- `assumptions`: list of `pl.Hypothesis(name, prop)`, `(name, prop)` tuples, a
  `{name: prop}` dict, or bare propositions (auto-named `h1`, `h2`, …). Order is kept.
- `thm.prove(tactic)`: attach a proof script (returns `thm`); does **not** verify.
- `thm.to_lean(project=None)`: deterministic Lean source (pure).
- `thm.verify(project=None, use_cache=True, timeout=None)` returns a `VerificationResult`.
- `thm.canonical()`: JSON-able canonical IR (used in fingerprints).

Statement validation (before Lean): every free variable declared, unique names, no
quantifier capture or shadowing, safe identifiers, proposition-valued statements.

### Decorator

```python
@pl.theorem(proof=None, name=None, assumptions=None, imports=())
def name(x: pl.Real, n: pl.Nat): return <proposition>
```

Each parameter needs a sort annotation (`*args`/`**kwargs` are rejected). `assumptions` is
a function of the same parameters returning anything `Theorem(assumptions=...)` accepts.
Bare `@pl.theorem` (no parentheses) also works. The result is a normal `pl.Theorem`.

### Display

`e.to_latex()`, `thm.to_latex()`, `pl.latex(obj)`; Jupyter uses `_repr_latex_` (expressions)
and `_repr_markdown_` (theorems, results). Names: `α`→`\alpha`, `x₁`/`x1`/`x_1`→`x_{1}`,
multi-letter names→`\mathit{...}`. Display only; never sent to Lean.

### Identifiers

ASCII letters, Greek letters (except `λ Π Σ`), digits, subscript digits `₀-₉`, `_`, `'`;
must start with a letter (or `_` + letter/digit); Lean keywords and core names are rejected.

## Tactics

| PyLeanX | Lean |
|---|---|
| `pl.ring()` | `ring` |
| `pl.positivity()` | `positivity` |
| `pl.omega()` | `omega` |
| `pl.simp(*lemmas, only=False, at=...)` | `simp [..] at ..` |
| `pl.linarith(*lemmas)`, `pl.nlinarith(*lemmas)` | `linarith [..]` |
| `pl.norm_num(*lemmas)` | `norm_num [..]` |
| `pl.intro("h", ...)` | `intro h ...` |
| `pl.exact(term)`, `pl.apply(term)` | `exact t`, `apply t` |
| `pl.rw(rule, pl.rev(rule2), at=...)` | `rw [rule, ← rule2] at ..` |
| `pl.use(e, ...)` | `use e, ...` |
| `pl.rfl()`, `pl.decide()`, `pl.constructor()`, `pl.assumption()` | same |
| `pl.steps(t1, t2)` or `t1 >> t2` | sequential tactics |
| `pl.branches(t1, t2)` | `· t1` / `· t2` bullets (one per goal) |
| `pl.raw_tactic(text, imports=())` | **untrusted** text; policy-gated |

Terms: a string is a hypothesis/lemma name (validated); `pl.ref("Nat.add_zero")`
references a library declaration (optionally with `imports=`); `pl.ref(theorem)`
references an earlier `Theorem`; calling a reference applies it:
`pl.ref("mul_pos")("ha", "hb")`, `pl.mathlib.sq_nonneg(x - 1)`.

## Verification

```python
results = pl.verify_all([thm1, thm2], project=None, use_cache=True, timeout=None)
```

`VerificationResult` fields: `theorem`, `status` (`verified`, `rejected`, `timeout`,
`environment_error`, `policy_rejected`), `verified` (property), `diagnostics`
(`Diagnostic`: severity, message, line, column, span_kind, span_label, python_origin),
`axioms`, `lean_source`, `toolchain`, `mathlib_revision`, `source_map`, `duration_ms`,
`cache_hit`, `fingerprint`, `policy`, `raw_tactics_used`. Methods: `summary()`,
`to_dict()`, `to_json()`, `from_dict()`.

## Interactive sessions (M5; `pip install 'pyleanx[interactive]'`)

```python
s = thm.session(project=None, timeout=600, launch="auto", preload=None)   # ProofSession
```

| Member | Meaning |
|---|---|
| `s.goals` | `Goals` (tuple of Lean goal strings) for the current state |
| `s.apply(*tactics)` | apply in order, stop at the first failure; returns `StepResult(ok, tactic, goals, error, status)` |
| `s.peek(tactic)` | try without recording |
| `s.undo(n=1)`, `s.reset()` | step back |
| `s.history`, `s.script` | applied tactics; `pl.steps(...)` of them |
| `s.is_complete` | the REPL reports no goals (**not** verification) |
| `s.finish()` | attach the script as `thm.proof` (requires completeness) |
| `s.verify()` | `finish()` + batch `thm.verify()`: the authoritative check |

- All sessions for a project share one persistent REPL; import environments are cached,
  so Mathlib loads once. `pl.shutdown_sessions()` stops the REPL processes.
- If a tactic needs a module that isn't loaded, the session re-imports and replays its
  history. If the REPL crashes or times out, it restarts and replays automatically.
- `preload`: extra modules imported up front. Default: common Mathlib tactics (`ring`,
  `positivity`, `linarith`, `norm_num`) when the statement already uses Mathlib.
- `launch`: `"binary"` runs LeanInteract's compiled `repl`; `"interpreted"` runs the same
  REPL program with the pinned `lean --run`; `"auto"` uses the binary unless the OS refuses
  to execute it (e.g. application control on managed Windows machines).
- Raw tactics follow the same policy gate and screening as the batch backend.

## Domain modules (M6)

Thin wrappers around Mathlib with concrete sorts. Each module has a `LEMMAS` catalog of
references (`pl.proofs.Name`, with the import each needs) checked by `#check` against the
pinned Mathlib (`VERIFIED_MATHLIB`). A reference asserts nothing; Lean checks every use.
The module docstrings list the abstractions and limitations.

| Module | Terms | Helpers / lemma examples |
|---|---|---|
| `pl.algebra` | (core arithmetic) | `identity(name, lhs, rhs)` (ring), `nonneg(name, e)` (positivity), `inequality(name, lhs, "<=", rhs, assumptions=…)` (nlinarith), `am_gm_two(name, a, b)`; `sq_nonneg`, `add_sq`, `sub_sq`, `abs_add_le`, `two_mul_le_add_sq`, … |
| `pl.analysis` | `sin`, `cos`, `pi()`, plus `sqrt`, `exp`, `log`, `abs_` | `sin_sq_add_cos_sq`, `sq_sqrt`, `exp_pos`, `add_one_le_exp`, `log_le_sub_one_of_pos`, `pi_pos`, … |
| `pl.geometry` | `Point` (= `EuclideanSpace ℝ (Fin 2)`), `point`, `points`, `dist`, `angle` | `dist_triangle`, `dist_comm`, `angle_comm`, `angle_add_angle_add_angle_eq_pi`, `pythagoras_iff`, … |

```python
A, B, C = geo.points("A B C")
pl.Theorem("angle_sum", [A, B, C], assumptions={"h": B != A},
           conclusion=geo.angle(A, B, C) + geo.angle(B, C, A) + geo.angle(C, A, B) == pl.pi(),
           proof=pl.exact(geo.angle_add_angle_add_angle_eq_pi(C, pl.hyp("h"))))
```

Points support only `=` and `≠`; ordering, arithmetic and numeric literals on points are
`SortError`s. `pl.sin`, `pl.cos`, `pl.pi` are also exported at top level.

## Theorem bank (M7)

A local, file-backed index (`~/.pyleanx/bank.json`, or `$PYLEANX_BANK`). Each entry keeps
a **canonical ID** (`geometry.dist_triangle`) separate from the **Lean name**
(`dist_triangle`), plus its formalization (system, toolchain, library revision), the
statement text and its SHA-256, assumptions, aliases, tags, provenance, dependency edges,
and, for theorems proved through PyLeanX, the verification evidence and canonical theorem.

```python
bank = pl.TheoremBank.open()               # or pl.TheoremBank(path); TheoremBank() = in memory
bank.index_catalogs()                      # one Lean run: statements come from `#check`
bank.index_declarations({"my.id": pl.ref("Nat.succ_le_of_lt", imports=[...])})
hits = bank.search("triangle inequality")  # ranked over IDs, names, aliases, tags, text
lemma = bank.ref("geometry.dist_triangle") # Name with imports; refuses other versions
bank.add_theorem(thm, result, id="my.lemma", dependencies=[...])  # verified results only
lemmas = bank.load_with_dependencies("my.lemma")   # rebuilt Theorems, deps first
pl.verify_all([*lemmas, main])             # reuse = re-check in the same Lean file
bank.link("my.lemma", "isabelle", "Foo.bar")   # informational; never used as equivalence
bank.save()
```

`ref`/`load` raise `VersionMismatchError` when the entry's toolchain or Mathlib revision
differs from the project's, and `CrossSystemError` for non-Lean entries. A bank entry is a
pointer, never a proof: anything it contributes is checked by Lean again.

`pl.theorem_from_canonical(data)` rebuilds a theorem from `Theorem.canonical()` JSON
exactly (strict: unknown sorts/functions/tactics are errors).

## Proof agents (M8): `pyleanx.agent`

| API | Purpose |
|---|---|
| `agent.ProofEnv(thm, project, allow_raw=False, max_steps=200)` | `observe()`, `act(text \| Tactic \| canonical JSON)`, `peek`, `undo`, `verify()`, `transcript`, `transcript_jsonl()` |
| `agent.TOOLS`, `env.call_tool(name, args)` | JSON-schema tools (`get_state`, `apply_tactic`, `undo`, `verify`) for tool-calling LLMs |
| `agent.tactic_from_text(text, allow_raw=False)` | common tactics → structured IR (with catalog imports); anything else → `RawTactic` only if allowed |
| `agent.AutomationProposer()`, `agent.RetrievalProposer(bank)`, `agent.ChainProposer(...)` | baseline proposers (`obs -> [tactic, ...]`) |
| `agent.search_proof(thm, proposer, project, max_depth, max_expansions)` | DFS with backtracking on the REPL → `ProofAttempt` |
| `agent.try_proofs(thm, candidates, project)` | REPL-free: candidates as renamed copies in one batch run; winner re-verified |
| `agent.basic()`, `agent.export_jsonl(path)`, `agent.run_benchmark(proposer, mode="session"\|"batch")` | 13-problem baseline set and scoring |

`ProofAttempt.verified` is true only when the batch backend verified the script.
`allow_raw=True` switches the project policy to `allow_raw_tactics=True` for that
environment: free-form text then runs after screening, and the final audit still
rejects `sorry`, foreign axioms and `native_decide`.

`pyleanx agent serve` speaks JSON lines on stdin/stdout:
`{"id":1,"method":"open","params":{"theorem":<canonical JSON>}}`, then `tools`,
`call` (`{"name":"apply_tactic","arguments":{"tactic":"ring"}}`), `transcript`, `close`.
Proofs inside submitted theorems are dropped; only the operator's `--allow-raw` enables
raw text.

## Projects and policy

```python
proj = pl.find_project()                       # see resolution order in project.py
proj = pl.LeanProject.at("path/to/lean-project", timeout=120,
                         import_mode="minimal",  # or "mathlib" => `import Mathlib`
                         extra_imports=("Mathlib.Tactic.Linarith",),
                         policy=pl.AxiomPolicy(allow_raw_tactics=False),
                         lean_options=(("maxHeartbeats", "400000"),),
                         unicode_types=False)    # True: ℝ ℕ ℤ ℚ in generated Lean
```

`pl.AxiomPolicy(allowed=STANDARD_AXIOMS, allow_native=False, allow_raw_tactics=False,
extra_allowed=frozenset())`. `sorryAx` is never accepted. `debug.*` Lean options are refused.

## CLI

```
pyleanx init [DIR] [--force] [--no-cache-get]
pyleanx doctor [--project P] [--json]
pyleanx show-lean SCRIPT [--project P] [--mathlib-imports] [--unicode-types]
pyleanx compile SCRIPT [-o OUT.lean]
pyleanx check SCRIPT [--json] [--include-source] [--no-cache] [--timeout S] [--allow-raw-tactics]
pyleanx cache stats|clear
pyleanx bank index|search|show|list [QUERY] [--bank FILE] [--json]
pyleanx agent bench [--mode session|batch] [--problems a,b] [--json]
pyleanx agent export [-o FILE.jsonl]
pyleanx agent serve [--allow-raw]
```

If Windows blocks the `pyleanx.exe` launcher, use `python -m pyleanx ...` (same arguments).

`check` exits 0 only if every theorem is verified; 1 otherwise; 2 on usage/script errors.

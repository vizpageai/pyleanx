# Troubleshooting

Start with `pyleanx doctor`. Each failing line includes a suggested fix.

| Symptom | Cause / fix |
|---|---|
| `lake on PATH: missing` | Install elan: https://lean-lang.org/install/manual/ and reopen the shell. |
| `project path ... (run pyleanx init)` | No workspace found. Run `pyleanx init`, or set `PYLEANX_PROJECT=/path/to/lean-project`. |
| `mathlib cache: missing` | Run `lake exe cache get` inside the project. Do **not** `lake build` Mathlib from source. |
| status `environment_error`, "imports failed to load" | Cache missing/partial, or an import module name does not exist in the pinned Mathlib. Check `result.diagnostics`. |
| `lean in project` shows another version | The project's `lean-toolchain` pins `v4.34.1`; elan installs it on first use. Do not edit the pin by hand. |
| status `timeout` | Increase `timeout=` / `--timeout`. The first run after boot is slower (olean loading from disk). |
| status `rejected` | Lean reported an error; `result.diagnostics` names the failing tactic step and the Python line it came from. |
| status `policy_rejected` | Proof compiled but depends on `sorryAx`, a non-standard axiom, native trust, or used `pl.raw_tactic` without permission. |
| `SymbolicTruthValueError` | You used `if`, `and`, `or`, `not`, a chained comparison or builtin `min/max` on symbolic expressions. Use `pl.And/Or/Not`, `pl.min/max`. |
| `SortError: sorts differ` | Mixed `Nat`/`Real` etc. Use `pl.cast(n, pl.Real)`. |
| `LiteralError` for `0.1` | Use `pl.real("0.1")` or `pl.rat(1, 10)`. |
| `UnicodeEncodeError` on Windows | Set `PYTHONIOENCODING=utf-8` when printing Lean source from your own scripts; the CLI does this automatically. |
| `` `foo` has already been declared `` | Your theorem name collides with a Mathlib/core declaration (e.g. `abs_nonneg`). Choose another name. |
| the first `thm.check()` takes minutes | It loads Mathlib into a Lean process that is then kept; later checks of the same import set take seconds. |
| `check` falls back to the batch backend ("fast REPL check was unavailable") | The REPL could not start or crashed, usually for lack of memory (each import set holds several GB). Close other programs, or lower `pyleanx.backend.repl_check.MAX_IMPORT_SETS` to 1; `pl.shutdown_sessions()` frees it. |
| `failed to read file '….olean.private'` when the REPL starts | The machine was out of memory (the file exists). Free memory and retry. |
| a step "ran out of time" (deterministic timeout) | State it in the same orientation as the cited fact (A ≠ C, not C ≠ A), cite fewer facts, or split it. `pl.explain_failure(thm, res)` names the step. |
| `“…” could mean several facts` | The description fits more than one fact equally well; use the fact's exact label or name (`pyleanx facts …` lists candidates). |
| `sanity_check`: "nothing was checked" | The hypotheses could not be sampled (an exact right angle, a function, a set). It proves nothing either way; Lean decides. |
| benchmark rows marked `stale` | The proof's generated Lean changed since it was checked; re-run `python benchmarks/naturalness.py --lean --only <module>`. |
| a lemma "unknown identifier" | Give its module: `pl.ref("foo", imports=["Mathlib.X.Y"])`, or use `LeanProject(import_mode="mathlib")`. |

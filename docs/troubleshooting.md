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
| a lemma "unknown identifier" | Give its module: `pl.ref("foo", imports=["Mathlib.X.Y"])`, or use `LeanProject(import_mode="mathlib")`. |

# Paste into Codex

Implement PyLeanX, a Python-native proof frontend for Lean 4, using the attached `IMPLEMENTATION_PLAN.md` and `AGENTS.md` as binding project specifications.

Start by inspecting the repository and environment. Implement milestones M0, then M1, M2, M3, and M4 sequentially. Build a real installable Python package using `src/pyleanx` with typed immutable symbolic expressions, theorem and tactic APIs, deterministic Lean source generation, and authoritative batch verification with the pinned Lean 4 + Mathlib toolchain.

Prioritize a working end-to-end proof:

```python
import pyleanx as pl
x, y = pl.symbols("x y", pl.Real)
thm = pl.Theorem("square_identity", variables=[x, y], conclusion=(x+y)**2 == x**2 + 2*x*y + y**2)
thm.prove(pl.ring())
result = thm.verify()
assert result.verified, result.diagnostics
print(thm.to_lean())
```

For final verification, do not stop at a success exit code or an empty proof state: audit transitive axiom dependencies, rejecting `sorryAx`, foreign axioms, and unapproved `_native` trust extensions. Use actual Mathlib cache setup (`lake exe cache get`) and lock toolchain versions. Implement both successful and deliberately failing Lean integration tests.

Use LeanInteract only after the batch MVP is verified and stable, for the separate interactive backend. Do not invent API signatures; inspect installed code or upstream docs. Build thorough Python unit tests, real Lean integration tests, source maps, diagnostics, a CLI, documentation, and continuous integration as described in the implementation plan.

Make incremental reviewable changes and commits. After each milestone, run tests and update `docs/roadmap.md`. If network or Lean setup is unavailable, implement what you can offline, document the exact blocker, and do not report an unverified milestone as complete. Do not ask routine design questions; follow the specification and make small documented decisions as needed.

Return the changed-file list, commands actually executed and exit statuses, verified theorem examples, negative-test outcomes, remaining blockers, and the next unfinished milestone.

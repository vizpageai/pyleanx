# Codex instructions: PyLeanX

You are implementing the project described in `IMPLEMENTATION_PLAN.md`. Read that file in full before coding. Implement M0 -> M4 before any substantial M5+ work.

## Nonnegotiable requirements

- Python is a frontend; Lean 4 and its kernel remain the formal verifier.
- Do not claim `verified=True` from mock results, mere tactic completion, Python symbolic simplification, or successful process exit without an axiom-dependency audit.
- Require an auditable `#print axioms` result or a structured equivalent; reject `sorryAx`, nonstandard axioms, and native-evaluation trust extensions by default.
- Do not use `sorry`/`admit` in actual proofs or to bypass tests. Negative-test fixtures may deliberately contain them.
- Do not reimplement Lean's dependent-type checker or kernel.
- Do not claim the package is a security sandbox: executing ordinary Python scripts runs arbitrary Python code.
- Do not publish as `pylean` on PyPI; the name is occupied. Use `pyleanx` provisionally.
- Lock Lean/Mathlib and dependencies. Run `lake exe cache get` rather than rebuilding all Mathlib when possible.
- Never destroy user work in a preexisting repository.

## Work protocol

1. Examine current code and installed tools.
2. Select the earliest incomplete milestone from the implementation plan.
3. Implement and test it; retain all tests in the repo.
4. Run real Lean integration tests when a Lean toolchain is present; disclose if unavailable.
5. Update `docs/roadmap.md` with commands, versions, test status, and blockers.
6. Make one scoped commit per milestone when in a git repo.
7. Give a clear status report; do not overstate what is implemented.

## Definition of verified

The exact Python theorem AST produces deterministic Lean source. Pinned Lean checks this source without errors. The transitive axiom audit succeeds under the declared policy. The result stores toolchain and dependency versions, source/fingerprint, diagnostics and audit evidence.

## Prioritize these examples

- Polynomial square identity by `ring`.
- Nonnegative square over Real by `positivity`.
- `n + 0 = n` by `simp`.
- `P -> P` by `intro` then `exact`.
- Negative tests for false statement, invalid tactic, `sorry` and user-added axioms.

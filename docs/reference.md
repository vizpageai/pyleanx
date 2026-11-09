# Python reference

Generated from the docstrings. For a guided overview with examples, see the
[API guide](api.md).

## Core

::: pyleanx.theorem
    options:
      members: [Theorem, Hypothesis, theorem]

::: pyleanx.binders
    options:
      members: [symbol, symbols, prop_symbol, free_vars]

::: pyleanx.expr
    options:
      members: [Expr, Var, Func, Eq, Ne, Le, Lt, Ge, Gt, Not, And, Or, Implies, Iff, Forall,
                Exists, cast, nat, integer, real, rat, sqrt, exp, log]

::: pyleanx.types
    options:
      members: [Sort, register_sort]

## Proofs

::: pyleanx.proofs
    options:
      members: [ring, omega, positivity, rfl, decide, constructor, assumption, linarith,
                nlinarith, norm_num, simp, intro, exact, apply, rw, rev, use, steps,
                branches, raw_tactic, ref, hyp, Name]

## Verification

::: pyleanx.backend.interface
    options:
      members: [VerificationResult, Status, Diagnostic]

::: pyleanx.backend.subprocess_backend
    options:
      members: [verify_all]

::: pyleanx.backend.audit
    options:
      members: [AxiomPolicy]

::: pyleanx.project
    options:
      members: [LeanProject, find_project]

## Interactive sessions

::: pyleanx.session
    options:
      members: [ProofSession, StepResult, Goals]

## Mathlib

::: pyleanx.algebra

::: pyleanx.analysis

::: pyleanx.geometry

::: pyleanx.infoview
    options:
      members: [infoview, DeclView, DeclViews, Binder]

::: pyleanx.bank
    options:
      members: [TheoremBank, BankEntry, Formalization, BankError, VersionMismatchError,
                CrossSystemError]

## Agents

::: pyleanx.agent

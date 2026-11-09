# Stability and versioning

## Version numbers

PyLeanX uses [semantic versioning](https://semver.org). During the `0.x` series:

- **patch** releases (`0.1.1`) fix bugs and never change the public API or the pinned
  Lean/Mathlib versions;
- **minor** releases (`0.2.0`) may change the public API (with a deprecation period where
  practical) and may move the pinned Lean/Mathlib versions.

`1.0` will freeze the public API under the usual semver rules.

## What is public

- Everything exported from `pyleanx` (`pl.__all__`), the domain modules
  (`pyleanx.algebra`, `pyleanx.analysis`, `pyleanx.geometry`) and `pyleanx.agent`.
- The CLI commands, their flags and exit codes.
- The JSON schema of `VerificationResult.to_dict()` (`schema_version`), the theorem bank
  file format (`schema`) and the canonical theorem JSON.

Modules and names starting with `_`, and `pyleanx.backend.*` internals not re-exported from
`pyleanx`, may change in any release.

## Deprecations

A deprecated public name keeps working for at least one minor release and emits a
`DeprecationWarning` that says what to use instead. Deprecations are listed in the
[changelog](https://github.com/vizpageai/pyleanx/blob/main/CHANGELOG.md).

## Lean and Mathlib pins

Each release pins exactly one Lean toolchain and one Mathlib revision (`lean-project/`,
`pyleanx doctor`). Mathlib renames and restates theorems frequently, so:

- a proof that verified with one PyLeanX release may need changes after a pin moves;
- every `VerificationResult` and theorem-bank entry records the toolchain and Mathlib
  revision, and bank entries refuse to be used with a different one;
- lemma catalogs are re-checked against the new Mathlib before each release
  (`PYLEANX_SLOW_TESTS=1 pytest tests/integration/test_domains_lean.py`).

## Soundness is not negotiable

No release, deprecation or compatibility shim may produce `verified=True` without a pinned
Lean run and a passing axiom audit. A soundness bug is fixed in a patch release with an
advisory (see [SECURITY.md](https://github.com/vizpageai/pyleanx/blob/main/SECURITY.md)).

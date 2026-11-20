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
- The core modules: `pyleanx.ops`, `pyleanx.derivation`, `pyleanx.justify`, `pyleanx.pack`,
  `pyleanx.packs`, `pyleanx.certifiers`, and `get_checker` / `register_checker` in
  `pyleanx.backend.interface` (the names each lists in `__all__`).
- The CLI commands, their flags and exit codes.
- The JSON schema of `VerificationResult.to_dict()` (`schema_version`), the theorem bank
  file format (`schema`) and the canonical theorem JSON.

Modules and names starting with `_`, and `pyleanx.backend.*` internals not re-exported from
`pyleanx`, may change in any release.

## Maturity of features

Public features carry one of two labels:

- **stable** (the default): covered by the rules above.
- **beta**: public and tested, but its behaviour may still be adjusted in a minor release
  without a deprecation period, based on use. In 0.1 these are the natural-proof tools:
  `Theorem.check` / `pl.check_all` (the REPL checker; its verdicts follow the same rules as
  `verify`, but caching and process management may change), `Theorem.sanity_check`,
  `pl.explain_failure` (the wording of explanations), `pl.fact` / `pl.search_facts` and
  descriptions in `because=` (which description selects which fact may improve), and
  `pl.similarly`, `pyleanx check --watch` (its output format), and the refusal of a cited
  hypothesis name that the proof never defines (which names count as hypothesis-like may
  change). The progress lines of the first `check` (stderr) are not an API. The heuristics of
  `benchmarks/naturalness.py` are not an API.
- **beta** in 0.2, the extension interface of the core, which domain packages are built
  on and which their first authors may still shape: `pl.domain_pack` / `DomainPack`, the
  rule and pack registry of `pyleanx.justify` (`register_pack`, `add_rule`), certifiers
  (`register_certifier`, `Goal`, `register_nonneg`, `DomainPack.certifier`), the
  `pyleanx.packs` entry point, `register_checker`, `Derivation.goal` /
  `Derivation.contexts` / `Derivation.certificates`, and `pyleanx.certifiers` (which
  certificates it finds may improve; a certificate is never trusted, Lean checks it).
  `pyleanx.ops` and the rest of `pyleanx.derivation` are stable.

Which alternatives the gap filler tries, and in which order, and which certificates the
certifiers propose, is not part of the API: a later release may close more steps (never
fewer is the aim, and the benchmarks measure it), and Lean checks whatever it produces.
Registering a domain pack, rule or certifier changes the Lean a proof generates, so a
result's fingerprint records it; a pack takes part only once imported, never implicitly.

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

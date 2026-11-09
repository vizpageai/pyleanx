# Security policy

## What counts as a vulnerability

For a proof checker the most serious bug is a **soundness bypass**: any way to obtain
`VerificationResult.verified == True` (or `pyleanx check` exit 0) for a statement that the
pinned Lean kernel did not prove under the declared axiom policy. Examples: spoofing the
`#print axioms` report, smuggling `sorry`, extra axioms or native evaluation past the audit,
making PyLeanX check different Lean source than it reports, or a cache entry that returns a
result for a different statement.

Also in scope: bugs where PyLeanX runs commands or writes files the user did not ask for,
and secrets leaking into results, caches or bank files.

Out of scope: PyLeanX executes the Python scripts you give it and runs Lean locally; it is
**not a sandbox** (see [docs/security.md](docs/security.md)). Bugs in Lean or Mathlib
themselves should go to their projects.

## Reporting

Please **do not open a public issue** for a soundness bypass. Use
[GitHub private vulnerability reporting](https://github.com/vizpageai/pyleanx/security/advisories/new)
and include a minimal script, the `pyleanx doctor --json` output and the observed result.
We aim to acknowledge within 7 days and to publish a fix and advisory once released.

## Supported versions

Only the latest release receives security fixes while PyLeanX is in the 0.x series.

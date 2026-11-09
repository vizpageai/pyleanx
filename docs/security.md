# Trust model and security

## PyLeanX is not a sandbox

- Using the library, or running `pyleanx show-lean/compile/check script.py`, **executes
  ordinary Python code** with your user's privileges. Only run scripts you trust.
- Lean itself runs as a normal local process. Lean files can run code at elaboration
  time (`#eval`, macros, tactics). PyLeanX-generated files only contain typed tactics,
  unless you opt into raw tactics.
- A hosted or multi-tenant service must add OS-level isolation (containers/VMs,
  CPU/memory/process quotas, no network, read-only filesystem except a scratch dir).
  That is out of scope for v0.1.

## What the verifier trusts

1. The Lean 4 kernel and elaborator of the pinned toolchain (`v4.34.1`).
2. The pinned Mathlib revision and its dependencies (`lean-project/lake-manifest.json`).
3. Prebuilt `.olean` files fetched by `lake exe cache get` from Mathlib's cache.
4. The three standard axioms `propext`, `Classical.choice`, `Quot.sound` (configurable).
5. That the generated file is not adversarial (see below).

## Audit details

- Every theorem is followed by `#print axioms <name>` at a line recorded in the source
  map. Only an `information` message at exactly that line, naming that theorem, counts.
  A proof cannot spoof it by printing similar text elsewhere.
- Missing, duplicated, or unparseable reports yield `policy_rejected`.
- `sorryAx` is always rejected (also covers elaboration errors recovered as `sorry`).
- Native trust (`Lean.ofReduceBool`, `Lean.trustCompiler`, `*_native*`) is rejected unless
  `AxiomPolicy(allow_native=True)`, and the result's `policy` field records that.
- `lean_options` named `debug.*` are refused; option names/values are restricted to safe
  characters and passed as argv entries (never through a shell).

## Raw (AI-generated) tactics

`pl.raw_tactic(text)` exists so proof agents can submit tactic text. It is untrusted:

1. Rejected (`policy_rejected`, Lean is not even run) unless
   `AxiomPolicy(allow_raw_tactics=True)` or `pyleanx check --allow-raw-tactics`.
2. Screened: no commands or declarations (`axiom`, `theorem`, `def`, `instance`, …),
   no `set_option`, no `#`-commands, no metaprogramming entry points (`run_tac`, `elab`,
   `macro`, `Lean.Elab`, …), no `debug.*`, no block comments, no control characters.
3. Then kernel-checked and audited like any other proof; `raw_tactics_used=True` is
   recorded in the result.

Screening is a heuristic defence-in-depth layer, not a proof of safety. For adversarial
settings (public leaderboards, hosted checking of untrusted submissions), additionally
replay the compiled environment through an independent checker such as `lean4checker`
or `comparator` (see Lean's "Validating Proofs" documentation). Not implemented yet.

## Interactive sessions

- The REPL (LeanInteract) is a *development aid*. Its goal states and "Completed" status
  are never used as evidence; `session.verify()` runs the batch backend in a fresh
  process with the full audit.
- The REPL is a long-lived Lean process that elaborates whatever tactics you send, the
  same trust level as running Lean locally. Raw tactic text is gated and screened as in
  batch mode.
- `launch="interpreted"` runs the REPL program with the pinned, already-installed `lean`
  (`lean --run`). PyLeanX uses it automatically only when the OS refuses to execute the
  freshly built `repl` binary. It does not move or disguise binaries to get around
  application-control policies; if you want the compiled binary on a managed machine,
  ask your administrator to allow it.

## Theorem bank

- Entries are pointers. Using one emits a name into Lean source, and the kernel checks
  that use; banked PyLeanX theorems are re-checked in the same Lean file as the proof
  that uses them (`load_with_dependencies` + `verify_all`). Stored evidence is a record,
  not a credential.
- Statements of library declarations come from Lean (`#check`) at the pinned revision.
  Each statement is stored with its SHA-256, entries carry their exact formalization, and
  `ref`/`load` refuse other toolchains or library revisions.
- Cross-system links (`bank.link`) and non-Lean entries are informational only.
  Equivalence between formalizations is never assumed.
- A bank file is data you chose to trust as an index. A tampered entry cannot make
  anything verified, but it can point you at a different lemma; check `entry.statement`.

## Proof agents and the agent server

- Agent actions run in the interactive REPL; `ProofAttempt.verified`/`verify` come only
  from the batch backend's fresh run and audit. The integration gate shows a `sorry` agent
  and a `native_decide` agent being rejected after the REPL accepted their steps.
- `allow_raw` is an explicit opt-in per environment (and per server via
  `pyleanx agent serve --allow-raw`); a client request cannot enable it.
- `pyleanx agent serve` executes Lean on statements supplied by the client. Run it only
  for clients you trust as you would trust someone running Lean on your machine: it is
  not a sandbox, has no resource accounting beyond timeouts and step budgets, and should
  not be exposed to a network.

## Statement faithfulness

The kernel certifies the **generated Lean statement**. PyLeanX makes that statement
visible (`thm.to_lean()`, `result.lean_source`) and avoids silent coercions, float
literals and name capture, but it cannot check that the formal statement says what you
meant informally.

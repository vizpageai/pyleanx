# The core

PyLeanX is to Lean what PyTorch is to its kernels: a Python front end whose core is small,
domain-free and extensible, and whose results are computed by an engine it does not
reimplement. This page states what belongs to the core, why, how it maps onto the way
Lean checks a proof, and the order in which it is built. It complements the
[foundations plan](foundations.md), which is about mathematical content built on the core.

## The equivalence

| PyTorch | PyLeanX core | Lean mechanism it drives |
|---|---|---|
| `Tensor` | **Statement**: a typed term in a context of variables and hypotheses (`expr`, `types`, `terms`, `binders`) | a *type* in `Prop` (Curry–Howard: a statement is a type, a proof a term of it) |
| tensor operations | **Statement operations**: substitute, exchange variables, instantiate, specialise a fact, free variables (`pyleanx.ops`) | instantiation and application of terms |
| autograd graph (recorded as you compute) | **Derivation graph**: each step, what it states and what it depends on, recorded as you write (`pyleanx.derivation`) | a tactic block of `have` steps, each adding a hypothesis to the local context |
| an op's registered derivative | **Justification rules** a vocabulary registers (`pyleanx.justify`) | the tactics tried inside each `have … := by first \| …` |
| `backward()` | **Justification**: for every step, generate the tactic search that proves it from what it cites | elaboration and tactic execution; the kernel re-checks the result |
| devices (CPU, CUDA) | **Kernels**: batch `lean` process, persistent REPL (`backend`) | the Lean kernel; `#print axioms` audit |
| gradients flow to the leaves | **Verdicts flow to the steps**: errors attributed to the step, explained in its words | message positions and goals (`⊢`) |
| eager mode / `torch.compile` | `sanity_check`, `check()` while writing / `verify()` for the record | REPL environment reuse / fresh process |
| `nn.Module`, torchvision | **Domain packs**: vocabulary, facts, rules, numeric samplers, notation | Mathlib theories and PyLeanX's shipped facts |
| optimizers, ADMM | **Proof methods** (induction, ε–δ, similar triangles, CZ decomposition) | built from the core's moves |
| datasets, training scripts | **Examples, lectures, notebooks** | tests of the core, written later |

## What the core contains

1. **Statements**: sorts, expressions, binders, definitions; a *declaration* mechanism
   (symbol, Lean name, sort, notation, imports). No particular mathematical symbol.
2. **Statement operations**: one API for the term algebra that proof moves are built from.
3. **Derivation graph**: the explicit structure of a written proof: nodes (hypotheses,
   steps, choices), edges (citations, scope), names. Scope checks, "similarly", error
   attribution and explanations read it.
4. **Justification engine**: a step is (goal, cited facts, local definitions, avoided
   facts); its tactic search is assembled from *rules* in ordered *slots*. The core ships
   the domain-free rules (hypotheses, cited facts, symmetry of `=`/`≠`, conjunction
   parts, application of lemmas to cited facts, rewriting, arithmetic decision procedures).
   A pack's rules are active in a theorem only when the theorem uses the pack's symbols.
5. **Compilation**: deterministic Lean with source maps and import closure.
6. **Kernels and trust**: pinned toolchain, batch and REPL checkers, transitive axiom audit,
   fingerprinted evidence and cache. Only this layer reports "verified", on Lean's word.
7. **Feedback frameworks**: attribution of Lean messages to steps; explanation hooks; the
   numeric sampling framework (evaluators and figure constructions are registered).
8. **Extension interface**: packs register vocabulary, facts, justification rules,
   numeric evaluators/constructions and notation. Adding a domain never edits the core.

Not in the core: any mathematical vocabulary beyond logic and the numeric prelude, any
facts, domain heuristics, examples and lectures, the theorem bank, agents, the CLI.

## Writing a domain pack

A pack declares itself once and registers everything it contributes through one object;
the core is never edited. The geometry pack (`pyleanx.geometry`) is written this way.

```py
import pyleanx as pl

topo = pl.domain_pack("topology", sorts={"TopSpace"}, symbols=("TopologicalSpace.",))
topo.facts("mypkg.topology", prefix="top", title="Topology")    # its LEMMAS, citable by name
topo.rule("step", 55, lambda s: [f"(simp only [interior_interior] at *; exact{s.h})"],
          name="interior idempotent")                           # a justification rule
topo.sampler("TopSpace", lambda rng: ...)                       # values for sanity checks
topo.hint(r"failed to synthesize TopologicalSpace", "say which topology the set carries")
```

Its rules apply only to theorems that use its sorts or symbols. Nothing a pack registers
is trusted: Lean checks every proof the rules help produce.

A pack can live in its own distribution: [`pyleanx-analysis`](domains.md) (in
`domains/analysis`) depends on `pyleanx`, announces itself through the `pyleanx.packs`
entry point, and is never imported by the core (a test enforces it). A package takes part
once it is imported, by the author or by `pyleanx.packs.load_plugins()` (used by
`pyleanx doctor` and `pyleanx facts`), never implicitly: the Lean a proof generates
depends only on the proof and the packages imported. For the same reason the core's
golden-Lean test runs in a fresh process, and a package's tests run in their own.

## Constraints from Lean's mechanism

* **Python never elaborates.** Implicit arguments, type-class instances, coercions and
  definitional unfolding are Lean's; the core only produces the surface text.
* **One budget per declaration.** Every alternative tried in every step of a theorem
  shares Lean's heartbeat budget, so rules are ordered cheap-first (`with_reducible`
  matching fails at once on a mismatch) and their number is bounded per step.
* **`first` reports only its last failure.** Explanations cannot rely on the error of the
  "right" alternative; they use the step's statement, citations and the remaining goal.
* **The kernel is the authority.** Any rule may be wrong; at worst a proof fails to
  check. No rule, cache or memo can make a step count as proved without Lean.

## Build order and gates

Every phase keeps all unit tests and the API snapshot green. The **golden Lean test**
records a fingerprint of the generated Lean of every written proof in the benchmark; a
phase that changes generated Lean must re-verify the affected proofs with Lean and update
the benchmark results (`benchmarks/lean_results.json`).

| Phase | Work | Gate |
|---|---|---|
| K0 | This page; golden Lean fingerprints; layering test of allowed imports | tests pass on the current code |
| K1 | Justification engine: rules in ordered slots; core rules; geometry rules moved to the geometry pack, active when a theorem uses geometry | geometry proofs: Lean byte-identical; other proofs: lose only geometry alternatives and re-verify with Lean |
| K2 | Derivation graph; scope checks and "similarly" read it | behaviour and Lean unchanged |
| K3 | Statement operations as one API | Lean unchanged |
| K4 | Numeric sampling framework; geometry evaluators and constructions move to the pack | sanity results unchanged on the benchmark |
| K5 | Packs for the remaining domains; fact registry with one `Fact` type | Lean unchanged |
| K6 | Remembered winners: the alternative that closed a step is recorded (REPL) and tried first next time | a measurable speed-up of warm re-checks; a step whose winner no longer applies falls back to the full search |
| K7 | Compact justification: write repeated parts of the search once per file as Lean macros | all 72 proofs re-verified with Lean; Lean's work measured before and after |

## Status (2026-11-19)

| Phase | State | Evidence |
|---|---|---|
| K0 | done | `tests/unit/test_core_layers.py`, `tests/golden/lean_fingerprints.json`, `scripts/golden_lean.py` |
| K1 | done | `pyleanx/justify.py`; geometry rules registered by `pyleanx/geometry.py`. Geometry proofs: Lean byte-identical. The other 55 proofs lost only geometry alternatives and were re-verified with Lean: all pass (benchmark 72/72) |
| K2 | done | `pyleanx/derivation.py`; the unknown-hypothesis check reads it (same names as before on all 72 proofs) |
| K3 | done | `pyleanx/ops.py`; pack activation uses `ops.vocabulary` |
| K4 | done | `pyleanx/numeric.py` registries; `pyleanx/_geometry_numeric.py`. Sanity reports of 77 cases identical, sampled values included |
| K5 | partly | fact-search registry and `pyleanx/packs.py` done. Facts already share one type (`Name`, with `LibraryFact` for facts proved in PyLeanX and `TheoremRef` for cited theorems). Still to do: the theorem bank's catalogue list (`_domain.all_catalogs`) from the registry, and exact statement contracts per fact ([foundations](foundations.md) F2) |
| K7 | done | The step-independent side-goal closers are one macro per file (`pyleanx_close_…`), called by every step. Lean's profiler on the 7 Euclid proofs: ≈38 s of work (parsing 19.1 s) before, ≈19 s (parsing 4.9 s) after; file 888 KB → 469 KB; all 72 proofs: 30.7 MB → 24.6 MB of Lean (the gain is largest in geometry, whose closers are longest), re-verified with Lean: 72/72. Writing *every* step's search as a macro was measured too and is worse (≈47 s): each macro is compiled like a program |
| K6 | tried, not kept | Implemented and measured on the 7 Euclid proofs (REPL): cold check 750 s (Mathlib import); warm re-checks 75 s and 70 s with remembered winners first, 70 s without. No gain: a warm check's time is not spent on failing alternatives. The change was reverted (it also made `check()` able to accept a step that `verify()` times out on). Next: profile where a warm check spends its time before optimising |

**Where a check spends its time** (Lean's profiler, batch run of the 7 Euclid proofs, 78 s
wall time including the import): parsing 14.5 s, elaboration 7.0 s, linting 5.5 s, tactic
execution 3.6 s, type-class inference 2.3 s, kernel type checking 0.4 s. The generated file
is 888 KB, because every step spells out its alternatives (and their side-goal closers) as
text. The search itself is cheap; *reading* it is not, which is why reordering it (K6) did
not help. K7 follows from this: a Lean macro defined once per file can build a step's
alternatives from its cited facts (checked with core Lean: a macro looping over the facts
proves steps by a reversed fact, by applying one fact to another and by `omega`, and
rejects a false step with the same error a `first` block gives).

Extension interface: `pl.domain_pack(...)` with `rule`, `facts`, `function`, `apply`,
`sampler`, `construction` and `hint` (explanation hints are now registrable); the geometry
pack is written with it (golden Lean and the 77 sanity reports unchanged).

Kernels: `Theorem.verify` and `Theorem.check` reach Lean through named checkers
(`backend.interface.get_checker("batch" | "repl")`); `register_checker` adds another
(a Lean on another machine). Registering a checker is trusting it, as the pinned Lean binary
is trusted: it must run Lean and the axiom audit on the exact generated source.

Import structure: there is no cycle among module-level imports (a test enforces it). Some
modules import others inside functions (late binding, e.g. a statement imports the
renderer when it is printed, as `torch.Tensor.__repr__` imports its formatter); a static
graph that counts those shows one large component, which is not an import-order problem.

Remaining domain knowledge in core modules: none of the geometry pack's names (enforced by
a test). The numeric prelude (ℝ, ℕ, ℤ, `Real.sqrt`, `exp`, `log`, `sin`, `cos`, `π`) and
general constructs (sums, integrals) stay in the core by design.

Status is also tracked in the [roadmap](roadmap.md).

# Libraries beyond Mathlib (example: OpenAI's Vlasov–Maxwell)

Mathlib is always available. Other Lean libraries are added to a project with
`pyleanx add`, and their declarations become Python objects through generated bindings.

## Adding a library

```bash
python -m pyleanx add oai https://github.com/openai/math \
    --rev 4eaee87548250b2682affda7d05d947c05554bae --subdir lean \
    --module ComparatorChallenges.VlasovMaxwell --module OAI.Analysis.VlasovMaxwell.Model \
    --lean-option autoImplicit=false
python -m pyleanx libs
```

`add`:

1. fetches the pinned commit (only the files needed),
2. follows the `import`s of the requested modules and vendors exactly that closure; imports
   outside the library must be Mathlib or its dependencies, otherwise it stops and says
   which package is missing,
3. checks the library was written for the project's Lean toolchain and Mathlib revision
   (compiled Lean files are version-specific),
4. compiles the modules with the pinned `lean` into `<project>/.pyleanx/libs/<name>/`
   (incrementally; `pyleanx build-lib oai` rebuilds), and records file hashes, the commit and
   the license (`NOTICE.txt`).

Compiled libraries are on Lean's search path for verification, sessions and bindings, and
their content hash is part of every verification fingerprint. The pinned Lake files are not
modified. Building a library runs its Lean code, like any Lean build.

## Generated bindings

```py
import pyleanx as pl

RVM = pl.lib.use("ComparatorChallenges.VlasovMaxwell").OAI.RVM
d = pl.var("d", RVM.Datum)          # Lean types are sorts
v = pl.var("v", RVM.Vec)
RVM.q(v)                            # definitions are functions:  OAI.RVM.q v
RVM.Admissible(d)                   # predicates give propositions
d.f0                                # structure fields (f₀ is spelled f0 in Python)
pl.lib.search("Classical")          # search loaded declarations
pl.lib.decl("OAI.RVM.q").type       # Lean's own statement
```

`pl.lib.use(module, …)` runs a small Lean program once to export the module's declarations
(cached per module set and pin configuration). For editor completion, generate a module:
`python -m pyleanx bindings ComparatorChallenges.VlasovMaxwell -o rvm.py`.

## Stating a library theorem faithfully

```py
s, s2 = pl.var("s", RVM.Solution), pl.var("s2", RVM.Solution)
main = pl.Theorem(
    "rvm_global_classical_solution", [d], assumptions={"hd": RVM.Admissible(d)},
    conclusion=pl.Exists(s, pl.And(
        RVM.Classical(d, s), RVM.SmoothOnFiniteHorizons(s),
        pl.Forall(s2, pl.Implies(RVM.Classical(d, s2), RVM.SameNonnegativeTime(s, s2))))))

main.same_statement_as("OAI.RVM.global_classical_solution")   # SAME statement
```

`same_statement_as` asks Lean to prove, by `rfl`, that the Python statement and the
library's statement are the same proposition, so a Python restatement can be checked
instead of trusted. A weakened version (for example existence only) is reported as not the
same.

## Proving with the library's definitions

```py
one_le_q = pl.Theorem(
    "rvm_one_le_q", [v], conclusion=pl.Le(1, RVM.q(v)),
    proof=pl.proof(
        pl.unfold(RVM.q),
        pl.have("h", pl.Le(1, 1 + pl.norm(v)**2), pl.auto(pl.ref("sq_nonneg")(pl.norm(v)))),
        pl.exact(pl.ref("Real.one_le_sqrt.mpr")("h"))))
one_le_q.verify()
```

Library theorems are cited like any lemma, `pl.exact(RVM.some_lemma(v))`, and the axiom
audit covers everything they depend on. In the challenge module, OAI's main theorem is stated
with a `sorry` proof (the real proof is the whole development); citing it is rejected with
`sorryAx` in the audit.

The complete, tested script is
[`examples/oai_vlasov_maxwell.py`](https://github.com/vizpageai/pyleanx/blob/main/examples/oai_vlasov_maxwell.py).
To use OAI's *proved* theorems, add the modules that prove them (for the main theorem,
`OAI.Analysis.VlasovMaxwell.Main`, about 200 files that take a long time to compile).

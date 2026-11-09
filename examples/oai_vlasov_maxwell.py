"""Working with OpenAI's relativistic Vlasov–Maxwell library from Python, without writing Lean.

One-time setup (vendors two modules that import only Mathlib, pinned to a commit):

    python -m pyleanx add oai https://github.com/openai/math \
        --rev 4eaee87548250b2682affda7d05d947c05554bae --subdir lean \
        --module ComparatorChallenges.VlasovMaxwell --module OAI.Analysis.VlasovMaxwell.Model \
        --lean-option autoImplicit=false

Then:  python examples/oai_vlasov_maxwell.py

1. The main theorem's *statement* is written in Python with OAI's own definitions, and Lean
   confirms it is definitionally the statement OAI proves (``same_statement_as``); a
   weakened variant is not.
2. A new theorem about OAI's definitions is proved in Python (structured proof).
3. Citing the challenge file's theorem (whose proof there is ``sorry``) is rejected by the
   axiom audit: nothing unproved can leak into a verified result.
"""

from __future__ import annotations

import pyleanx as pl

RVM = pl.lib.use("ComparatorChallenges.VlasovMaxwell").OAI.RVM
MAIN = "OAI.RVM.global_classical_solution"


def statements() -> tuple[pl.Theorem, pl.Theorem]:
    d = pl.var("d", RVM.Datum)
    s, s2 = pl.var("s", RVM.Solution), pl.var("s2", RVM.Solution)
    unique = pl.Forall(s2, pl.Implies(RVM.Classical(d, s2), RVM.SameNonnegativeTime(s, s2)))
    main = pl.Theorem(
        "rvm_global_classical_solution", [d], assumptions={"hd": RVM.Admissible(d)},
        conclusion=pl.Exists(s, pl.And(RVM.Classical(d, s), RVM.SmoothOnFiniteHorizons(s),
                                       unique)))
    weaker = pl.Theorem(  # existence only: drops smoothness and uniqueness
        "rvm_existence_only", [d], assumptions={"hd": RVM.Admissible(d)},
        conclusion=pl.Exists(s, RVM.Classical(d, s)))
    return main, weaker


def one_le_q() -> pl.Theorem:
    v = pl.var("v", RVM.Vec)
    return pl.Theorem(
        "rvm_one_le_q", [v], conclusion=pl.Le(1, RVM.q(v)),
        proof=pl.proof(
            pl.unfold(RVM.q),
            pl.have("h", pl.Le(1, 1 + pl.norm(v) ** 2), pl.auto(pl.ref("sq_nonneg")(pl.norm(v)))),
            pl.exact(pl.ref("Real.one_le_sqrt.mpr")("h"))))


def cheat() -> pl.Theorem:
    d = pl.var("d", RVM.Datum)
    s = pl.var("s", RVM.Solution)
    return pl.Theorem(
        "rvm_cites_unproved", [d], assumptions={"hd": RVM.Admissible(d)},
        conclusion=pl.Exists(s, RVM.Classical(d, s)),
        proof=pl.proof(pl.obtain("s hs", RVM.global_classical_solution(d, "hd")),
                       pl.exact(pl.ref("Exists.intro")(pl.var("s", RVM.Solution), "hs.left"))))


if __name__ == "__main__":
    main, weaker = statements()
    print(main.to_lean(audit=False).split("set_option autoImplicit false")[1].strip())
    same = main.same_statement_as(MAIN, timeout=3600)
    print(same.summary())
    differs = weaker.same_statement_as(MAIN, timeout=3600)
    print(differs.summary())
    results = pl.verify_all([one_le_q(), cheat()], timeout=3600)
    for r in results:
        print(r.summary())
    ok = (same.same and not differs.same and results[0].verified
          and not results[1].verified)
    print("all expectations met" if ok else "UNEXPECTED RESULT")
    raise SystemExit(0 if ok else 1)

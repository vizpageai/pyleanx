"""AI-style workflow: many candidate proofs checked in one Lean process, JSON out.

A proof agent would generate `candidates`; PyLeanX checks each one with Lean and
the axiom audit. Untrusted tactic text must be explicitly allowed by the policy.
"""

import dataclasses
import json

import pyleanx as pl

x = pl.symbol("x", pl.Real)
goal = (x - 1) ** 2 >= 0

candidates = {
    "cand_ring": pl.ring(),                                   # wrong tactic
    "cand_positivity": pl.positivity(),                       # works
    "cand_llm_text": pl.raw_tactic("nlinarith [sq_nonneg (x - 1)]",
                                   imports=["Mathlib.Tactic.Linarith"]),  # untrusted text
}
THEOREMS = [pl.Theorem(name, [x], conclusion=goal, proof=tac) for name, tac in candidates.items()]

if __name__ == "__main__":
    project = pl.find_project()
    project = project.with_(policy=dataclasses.replace(project.policy, allow_raw_tactics=True))
    for r in pl.verify_all(THEOREMS, project=project):
        print(json.dumps({"theorem": r.theorem, "status": r.status.value,
                          "axioms": r.axioms, "raw": r.raw_tactics_used,
                          "errors": [d.message for d in r.errors]}, ensure_ascii=False))

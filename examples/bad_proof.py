"""Deliberately failing examples: none of these may ever be reported as verified.

`pyleanx check examples/bad_proof.py` must exit nonzero.
"""

import pyleanx as pl

x, y = pl.symbols("x y", pl.Real)

# A false statement: no tactic can prove it.
false_claim = pl.Theorem("false_claim", variables=[x], conclusion=x**2 < 0, proof=pl.positivity())

# A true statement with an inappropriate tactic.
wrong_tactic = pl.Theorem("wrong_tactic", variables=[x, y], conclusion=x * y >= 0,
                          proof=pl.ring())

THEOREMS = [false_claim, wrong_tactic]

if __name__ == "__main__":
    for r in pl.verify_all(THEOREMS):
        print(r.summary())

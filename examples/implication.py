"""P -> P, and a hypothesis-using linear-arithmetic example."""

import pyleanx as pl

P = pl.prop_symbol("P")
identity_imp = pl.Theorem("identity_imp", variables=[P], conclusion=pl.Implies(P, P))
identity_imp.prove(pl.steps(pl.intro("h"), pl.exact("h")))  # or: pl.intro("h") >> pl.exact("h")

a, b = pl.symbols("a b", pl.Real)
sum_pos = pl.Theorem(
    "sum_pos",
    variables=[a, b],
    assumptions=[pl.Hypothesis("ha", a > 0), pl.Hypothesis("hb", b > 0)],
    conclusion=a + b > 0,
    proof=pl.linarith(),
)

THEOREMS = [identity_imp, sum_pos]

if __name__ == "__main__":
    for r in pl.verify_all(THEOREMS):
        print(r.summary())

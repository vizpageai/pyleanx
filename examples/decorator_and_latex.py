"""@pl.theorem, Greek names and LaTeX display.

In Jupyter, just evaluate `square_identity` or `amgm_two` in a cell: the statement is
typeset, with the generated Lean in a collapsible block. Expressions display as math.
"""

import pyleanx as pl


@pl.theorem(proof=pl.ring())
def square_identity(x: pl.Real, y: pl.Real):
    return (x + y) ** 2 == x**2 + 2 * x * y + y**2


@pl.theorem(proof=pl.nlinarith(pl.mathlib.sq_nonneg("α")),  # names refer to the binders
            assumptions=lambda α, β: {"hβ": β >= 0})
def greek_bound(α: pl.Real, β: pl.Real):
    return α**2 + β >= 0


THEOREMS = [square_identity, greek_bound]

if __name__ == "__main__":
    for thm in THEOREMS:
        print("LaTeX:", thm.to_latex())
    print(greek_bound.to_lean(pl.find_project().with_(unicode_types=True)))
    for r in pl.verify_all(THEOREMS):
        print(r.summary())

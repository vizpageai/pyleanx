"""Bernoulli's inequality by induction: (1 + x)ⁿ ≥ 1 + nx for x ≥ −1, checked by Lean.

Run:  python examples/readable_bernoulli.py
"""

from __future__ import annotations

import pyleanx as pl

x = pl.symbol("x", pl.Real)
n, k = pl.symbols("n k", pl.Nat)


def real(m):
    return pl.cast(m, pl.Real)


bernoulli = pl.Theorem(
    "bernoulli_inequality", [x, n],
    assumptions={"hx": x >= -1},
    conclusion=(1 + x)**n >= 1 + real(n) * x,
    proof=pl.induction_on(
        n, k=k,
        base=[pl.conclude(note="both sides are 1")],
        step=[
            pl.claim(1 + x >= 0, because="hx", name="hx1"),
            pl.claim(real(k) * x**2 >= 0, name="hsq", note="k ≥ 0 and x² ≥ 0"),
            pl.chain((1 + x)**(k + 1),
                     ("=", (1 + x)**k * (1 + x)),
                     (">=", (1 + real(k) * x) * (1 + x), ["ih", "hx1"],
                      "induction hypothesis, and 1 + x ≥ 0"),
                     ("=", 1 + real(k + 1) * x + real(k) * x**2),
                     (">=", 1 + real(k + 1) * x, "hsq")),
        ],
    ),
)

if __name__ == "__main__":
    result = bernoulli.verify(timeout=1800)
    print(bernoulli.prose(result))
    raise SystemExit(0 if result.verified else 1)

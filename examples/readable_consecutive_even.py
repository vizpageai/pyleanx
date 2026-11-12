"""n(n + 1) is even: a proof by cases (n even / n odd), checked by Lean.

Run:  python examples/readable_consecutive_even.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import numbers as nt

n, k = pl.symbols("n k", pl.Nat)

consecutive_even = pl.Theorem(
    "product_of_consecutive_is_even", [n],
    conclusion=nt.even(n * (n + 1)),
    proof=pl.proof(
        pl.cases_on(
            pl.case(nt.even(n),
                    pl.choose(k, such_that=n == 2 * k, because=[nt.even_iff_two_mul, "h"],
                              names="hk"),
                    pl.take(k * (n + 1), note="n(n + 1) = 2k(n + 1) = k(n + 1) + k(n + 1)"),
                    pl.conclude(because="hk")),
            pl.case(nt.odd(n),
                    pl.choose(k, such_that=n == 2 * k + 1, because="h", names="hk"),
                    pl.take((2 * k + 1) * (k + 1),
                            note="n + 1 = 2(k + 1), so n(n + 1) = 2(2k + 1)(k + 1)"),
                    pl.conclude(because="hk")),
            because=nt.even_or_odd,
        ),
    ),
)

if __name__ == "__main__":
    result = consecutive_even.verify(timeout=1800)
    print(consecutive_even.prose(result))
    raise SystemExit(0 if result.verified else 1)

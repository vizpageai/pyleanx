"""The sum of the first n odd numbers is n², by induction, checked by Lean.

    1 + 3 + 5 + … + (2n − 1) = n²

The inductive step splits off the last term of the sum, uses the induction hypothesis and
finishes with algebra. ``sum_of_odd_numbers.sanity_check()`` tries the identity (and a
wrong variant is reported with a value of n) before Lean runs.

Run:  python examples/readable_odd_sum.py
"""

from __future__ import annotations

import pyleanx as pl

n, k = pl.symbols("n k", pl.Nat)

#: ∑_{i < m} f(i + 1) = ∑_{i < m} f(i) + f(m): split off the last term
sum_range_succ = pl.ref("Finset.sum_range_succ",
                        imports=["Mathlib.Algebra.BigOperators.Group.Finset.Basic"])


def odd_sum(m: object) -> pl.Expr:
    """1 + 3 + … + (2m − 1) = ∑_{i < m} (2i + 1)."""
    return pl.sum(pl.finset_range(m), lambda i: 2 * i + 1, sort=pl.Nat)


sum_of_odd_numbers = pl.Theorem(
    "sum_of_odd_numbers", [n],
    conclusion=odd_sum(n) == n ** 2,
    proof=pl.induction_on(
        n, k=k,
        base=[pl.conclude(note="the empty sum is 0")],
        step=[
            pl.chain(odd_sum(k + 1),
                     ("=", odd_sum(k) + (2 * k + 1), sum_range_succ,
                      "split off the last term"),
                     ("=", k ** 2 + (2 * k + 1), "ih", "induction hypothesis"),
                     ("=", (k + 1) ** 2)),
        ],
    ),
)

THEOREMS = [sum_of_odd_numbers]

if __name__ == "__main__":
    print(sum_of_odd_numbers.sanity_check())
    result = sum_of_odd_numbers.verify(timeout=1800)
    print(sum_of_odd_numbers.prose(result))
    raise SystemExit(0 if result.verified else 1)

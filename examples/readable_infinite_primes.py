"""Euclid: there are infinitely many primes, written as in a textbook and checked by Lean.

For every n there is a prime p > n.

Proof: let N = n! + 1. Since n! > 0, N ≠ 1, so N has a prime factor p. If p ≤ n, then p ∣ n!, and
since p ∣ n! + 1 also p ∣ 1, which is impossible for a prime. So p > n.

Run:  python examples/readable_infinite_primes.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import numbers as nt

n, p, N = pl.symbols("n p N", pl.Nat)

infinitely_many_primes = pl.Theorem(
    "infinitely_many_primes", [n],
    conclusion=pl.Exists(p, pl.And(n < p, nt.prime(p))),
    proof=pl.proof(
        pl.let(N, nt.factorial(n) + 1),
        pl.claim(nt.factorial(n) > 0, because=nt.factorial_pos),
        pl.claim(N != 1, note="n! > 0, so N ≥ 2"),
        pl.choose(p, such_that=pl.And(nt.prime(p), nt.divides(p, N)),
                  because=nt.exists_prime_dvd, names="hp hpN"),
        pl.take(p),
        pl.claim(n < p, proof=pl.proof(
            pl.suppose_not(p <= n, name="hle"),
            pl.claim(nt.divides(p, nt.factorial(n)), because=[nt.dvd_factorial, nt.prime_pos]),
            pl.claim(nt.divides(p, 1), because=nt.dvd_add_right, note="p ∣ n! and p ∣ n! + 1"),
            pl.conclude(because=nt.prime_not_dvd_one),
        )),
        pl.conclude(),
    ),
)

if __name__ == "__main__":
    result = infinitely_many_primes.verify(timeout=1800)
    print(infinitely_many_primes.prose(result))
    raise SystemExit(0 if result.verified else 1)

"""n + 0 = n for natural numbers, proved by `simp` (and by `omega`)."""

import pyleanx as pl

n = pl.symbol("n", pl.Nat)

nat_add_zero = pl.Theorem("nat_add_zero", variables=[n], conclusion=n + 0 == n)
nat_add_zero.prove(pl.simp())

nat_add_zero_omega = pl.Theorem(
    "nat_add_zero_omega", variables=[n], conclusion=n + 0 == n, proof=pl.omega()
)

THEOREMS = [nat_add_zero, nat_add_zero_omega]

if __name__ == "__main__":
    for r in pl.verify_all(THEOREMS):
        print(r.summary())

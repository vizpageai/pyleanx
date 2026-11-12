"""A group in which every element squares to 1 is abelian, checked by Lean.

Proof: every x satisfies x·x = 1, so x⁻¹ = x. Hence ab = (ab)⁻¹ = b⁻¹a⁻¹ = ba.

Run:  python examples/readable_group_abelian.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import algebra as alg

G = alg.group("G")                     # Let G be a group.
a, b, x = pl.symbols("a b x", G)
inv = alg.inv

abelian = pl.Theorem(
    "abelian_of_sq_eq_one", [a, b],
    assumptions={"h": pl.Forall(x, x * x == 1)},
    conclusion=a * b == b * a,
    proof=pl.proof(
        pl.claim(pl.Forall(x, inv(x) == x), because=[alg.inv_eq_of_mul_eq_one, "h"],
                 name="self_inverse", note="x·x = 1, so x is its own inverse"),
        pl.chain(a * b,
                 ("=", inv(a * b), "self_inverse"),
                 ("=", inv(b) * inv(a), alg.mul_inv_rev),
                 ("=", b * a, "self_inverse")),
    ),
)

if __name__ == "__main__":
    result = abelian.verify(timeout=1800)
    print(abelian.prose(result))
    raise SystemExit(0 if result.verified else 1)

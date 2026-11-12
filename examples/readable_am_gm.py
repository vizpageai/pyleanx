"""AM–GM for two numbers, proved the classical way, and checked by Lean.

For a, b ≥ 0:  √(ab) ≤ (a + b)/2.

Proof: 0 ≤ (√a − √b)² = a − 2√a√b + b, and √a√b = √(ab).

Run:  python examples/readable_am_gm.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import analysis as an

a, b = pl.symbols("a b", pl.Real)
sqrt = pl.sqrt

am_gm = pl.Theorem(
    "am_gm_two", [a, b],
    assumptions={"ha": 0 <= a, "hb": 0 <= b},
    conclusion=sqrt(a * b) <= (a + b) / 2,
    proof=pl.proof(
        pl.claim((sqrt(a) - sqrt(b))**2 >= 0, note="a square is never negative"),
        pl.claim(sqrt(a)**2 == a, because=an.sq_sqrt),
        pl.claim(sqrt(b)**2 == b, because=an.sq_sqrt),
        pl.claim(sqrt(a * b) == sqrt(a) * sqrt(b), because=an.sqrt_mul),
        pl.conclude(note="expand the square"),
    ),
)

if __name__ == "__main__":
    result = am_gm.verify(timeout=1800)
    print(am_gm.prose(result))
    raise SystemExit(0 if result.verified else 1)

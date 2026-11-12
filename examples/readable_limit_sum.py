"""The limit of a sum is the sum of the limits, by the ε–N definition, checked by Lean.

If aₙ → A and bₙ → B, then aₙ + bₙ → A + B.

Proof: let ε > 0. Choose N₁ with |aₙ − A| < ε/2 for n ≥ N₁, and N₂ with |bₙ − B| < ε/2
for n ≥ N₂. For n ≥ max(N₁, N₂):
|aₙ + bₙ − (A + B)| ≤ |aₙ − A| + |bₙ − B| < ε/2 + ε/2 = ε.

Run:  python examples/readable_limit_sum.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import analysis as an

seq = pl.Fn(pl.Nat, pl.Real)
a, b = pl.symbols("a b", seq)
A, B, eps = pl.symbols("A B ε", pl.Real)
n, N1, N2 = pl.symbols("n N₁ N₂", pl.Nat)


def eps_N(term, limit):
    """∀ ε > 0, ∃ N, ∀ n ≥ N, |term(n) − limit| < ε (fresh bound variables each time)."""
    e = pl.symbol("ε", pl.Real)
    N, m = pl.symbols("N n", pl.Nat)
    return pl.Forall(e, pl.Implies(e > 0, pl.Exists(N, pl.Forall(
        m, pl.Implies(m >= N, pl.abs(term(m) - limit) < e)))))


def close_after(N, term, limit):
    """∀ n ≥ N, |term(n) − limit| < ε/2."""
    m = pl.symbol("n", pl.Nat)
    return pl.Forall(m, pl.Implies(m >= N, pl.abs(term(m) - limit) < eps / 2))


limit_of_sum = pl.Theorem(
    "limit_of_sum", [a, b, A, B],
    assumptions={"hA": an.tendsto(a, A), "hB": an.tendsto(b, B)},
    conclusion=an.tendsto(pl.fun(lambda m: a(m) + b(m), pl.Nat), A + B),
    proof=pl.proof(
        pl.claim(eps_N(a, A), because=[an.tendsto_iff, "hA"], name="hA_eps"),
        pl.claim(eps_N(b, B), because=[an.tendsto_iff, "hB"], name="hB_eps"),
        pl.suffices(eps_N(lambda m: a(m) + b(m), A + B), because=an.tendsto_iff),
        pl.fix(eps, assume={"hε": eps > 0}),
        pl.choose(N1, such_that=close_after(N1, a, A), because="hA_eps", names="hN₁",
                  note="apply aₙ → A with ε/2"),
        pl.choose(N2, such_that=close_after(N2, b, B), because="hB_eps", names="hN₂",
                  note="apply bₙ → B with ε/2"),
        pl.take(pl.max(N1, N2)),
        pl.fix(n, assume={"hn": n >= pl.max(N1, N2)}),
        pl.claim(pl.abs(a(n) - A) < eps / 2, because="hN₁", note="n ≥ N₁"),
        pl.claim(pl.abs(b(n) - B) < eps / 2, because="hN₂", note="n ≥ N₂"),
        pl.chain(pl.abs(a(n) + b(n) - (A + B)),
                 ("=", pl.abs((a(n) - A) + (b(n) - B)), None, "rearrange"),
                 ("<=", pl.abs(a(n) - A) + pl.abs(b(n) - B), an.triangle_inequality),
                 ("<", eps / 2 + eps / 2, None, "steps 9 and 10"),
                 ("=", eps)),
    ),
)

if __name__ == "__main__":
    result = limit_of_sum.verify(timeout=1800)
    print(limit_of_sum.prose(result))
    raise SystemExit(0 if result.verified else 1)

"""(x + y)^2 = x^2 + 2xy + y^2 over the reals, proved by `ring`."""

import pyleanx as pl

x, y = pl.symbols("x y", pl.Real)

square_identity = pl.Theorem(
    "square_identity",
    variables=[x, y],
    conclusion=(x + y) ** 2 == x**2 + 2 * x * y + y**2,
)
square_identity.prove(pl.ring())

THEOREMS = [square_identity]

if __name__ == "__main__":
    print(square_identity.to_lean())
    result = square_identity.verify()
    print(result.summary())
    assert result.verified, result.diagnostics

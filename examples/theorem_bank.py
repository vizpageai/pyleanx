"""Theorem bank: search a Lean-indexed catalog, use a hit in a proof, bank the result.

Run: python examples/theorem_bank.py   (first run asks Lean for every catalog statement)
"""

from pathlib import Path

import pyleanx as pl
from pyleanx import geometry as geo

bank = pl.TheoremBank.open(Path("example-bank.json"))
if "geometry.dist_triangle" not in bank:
    print("indexing catalogs with Lean (one run)...")
    bank.index_catalogs(timeout=1800)
    bank.save()

for hit in bank.search("triangle inequality", limit=3):
    print(f"{hit.score:4.1f}", hit.entry.summary())

entry = bank.get("triangle inequality")  # alias -> geometry.dist_triangle
print("\nexact statement at", entry.formalization.describe(), ":\n ", entry.statement)

A, B, C = geo.points("A B C")
thm = pl.Theorem("tri_ineq_plane", [A, B, C],
                 conclusion=geo.dist(A, C) <= geo.dist(A, B) + geo.dist(B, C),
                 proof=pl.exact(bank.ref(entry.id)(A, B, C)))
result = thm.verify(timeout=1800)
print("\n" + result.summary())

if result.verified:
    bank.add_theorem(thm, result, id="examples.tri_ineq_plane", replace=True,
                     aliases=["plane triangle inequality"])
    bank.save()
    print("banked with evidence:", bank.get("examples.tri_ineq_plane").evidence["fingerprint"][:16])
else:
    raise SystemExit(1)

"""Which bookkeeping steps does a domain pack make unnecessary? Lean decides.

    python benchmarks/pack_ablation.py MODULE[,MODULE…] [--pack pyleanx_analysis]

For each written proof of the modules, a variant is built with every top-level
bookkeeping step removed (positivity, distinctness, measure-theoretic side conditions, as
classified by ``naturalness.bookkeeping_kind``) and every citation of a removed step
dropped. The variants are checked by Lean with the pack imported; a variant that is
verified shows that the pack (and the core's rules) supply those steps.
"""

from __future__ import annotations

import dataclasses
import importlib
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "benchmarks"), str(ROOT / "examples")]

import naturalness as nb  # noqa: E402

import pyleanx as pl  # noqa: E402
from pyleanx.expr import Expr  # noqa: E402
from pyleanx.proofs import Claim, Name, Steps, Tactic  # noqa: E402


def _drop_citations(t: Any, removed: set[str]) -> Any:
    """``t`` with citations of ``removed`` names taken out, at every depth."""
    if isinstance(t, tuple):
        return tuple(_drop_citations(x, removed) for x in t)
    if not (dataclasses.is_dataclass(t) and isinstance(t, Tactic)) or isinstance(t, Expr):
        return t
    changes: dict[str, Any] = {}
    for f in dataclasses.fields(t):
        old = getattr(t, f.name)
        if f.name == "facts" and isinstance(old, tuple):
            new: Any = tuple(x for x in old if not (isinstance(x, Name) and x.name in removed))
        elif f.name == "links" and isinstance(old, tuple):
            new = tuple((op, e, tuple(x for x in fs if not (isinstance(x, Name)
                                                            and x.name in removed)), note)
                        for op, e, fs, note in old)
        elif isinstance(old, (Tactic, tuple)):
            new = _drop_citations(old, removed)
        else:
            continue
        if new is not old and not _same(new, old):
            changes[f.name] = new
    return dataclasses.replace(t, **changes) if changes else t


def _same(a: Any, b: Any) -> bool:
    if isinstance(a, tuple) and isinstance(b, tuple):
        return len(a) == len(b) and all(_same(x, y) for x, y in zip(a, b, strict=True))
    return a is b


def without_bookkeeping(thm: pl.Theorem) -> tuple[pl.Theorem, list[str]] | None:
    """The proof with its top-level bookkeeping steps removed (None if it has none)."""
    hyps = [h.prop for h in thm.assumptions]
    steps = list(thm.proof.tactics) if isinstance(thm.proof, Steps) else [thm.proof]
    removed = [s for s in steps if isinstance(s, Claim) and s.prop is not None
               and nb.bookkeeping_kind(s.prop, hyps) and s.proof is None]
    if not removed:
        return None
    names = {s.name for s in removed}
    gone = {id(s) for s in removed}   # identity: == on statements builds an equation
    kept = [_drop_citations(s, names) for s in steps if id(s) not in gone]
    variant = pl.Theorem(f"{thm.name}_lean", list(thm.variables),
                         assumptions={h.name: h.prop for h in thm.assumptions},
                         conclusion=thm.conclusion, proof=pl.proof(*kept))
    return variant, sorted(names)


def main(argv: list[str]) -> int:
    pack = "pyleanx_analysis"
    if "--pack" in argv:
        pack = argv[argv.index("--pack") + 1]
    importlib.import_module(pack)
    modules = set(argv[0].split(","))
    variants = []
    for _, m, t in nb.collect():
        if m in modules and (v := without_bookkeeping(t)) is not None:
            variants.append((t, *v))
    results = pl.verify_all([v for _, v, _ in variants], timeout=3600, use_cache=False)
    ok = 0
    for (t, _variant, names), r in zip(variants, results, strict=True):
        ok += r.verified
        print(f"{'removable' if r.verified else 'still needed':12s} {t.name}: "
              f"{len(names)} bookkeeping step(s) {names}", flush=True)
        if not r.verified:
            for d in r.errors[:2]:
                print("     ", d.span_label, "|", d.message.splitlines()[0][:150], flush=True)
    print(f"{ok}/{len(variants)} proofs verified without their bookkeeping steps")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

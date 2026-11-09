"""A small benchmark of statements (no proofs) for proof agents, and a runner.

``BASIC`` mixes logic, Nat, algebra, inequalities, analysis and geometry at an
introductory level. It is a smoke-test/baseline set, not a research benchmark;
use :func:`export_jsonl` to hand the statements (canonical JSON + Lean text) to an
external agent, and :func:`run_benchmark` to score a proposer with Lean.
"""

from __future__ import annotations

import json
import time
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from ..project import LeanProject
    from ..theorem import Theorem
    from .search import Proposer


@dataclass(frozen=True)
class Problem:
    name: str
    build: Callable[[], Theorem]
    tags: tuple[str, ...] = ()
    reference: str = ""  # a known proof (Lean tactic text), for documentation only


def _basic() -> list[Problem]:
    import pyleanx as pl
    from pyleanx import analysis as an
    from pyleanx import geometry as geo

    def p_imp():
        P = pl.prop_symbol("P")
        return pl.Theorem("b_imp_self", [P], conclusion=pl.Implies(P, P))

    def p_and_comm():
        P, Q = pl.prop_symbol("P"), pl.prop_symbol("Q")
        return pl.Theorem("b_and_comm", [P, Q], assumptions={"h": P & Q},
                          conclusion=Q & P)

    def p_nat_add_zero():
        n = pl.symbol("n", pl.Nat)
        return pl.Theorem("b_nat_add_zero", [n], conclusion=n + 0 == n)

    def p_nat_mul_one():
        n = pl.symbol("n", pl.Nat)
        return pl.Theorem("b_nat_mul_one", [n], conclusion=n * 1 == n)

    def p_nat_lt():
        n = pl.symbol("n", pl.Nat)
        return pl.Theorem("b_nat_lt_succ", [n], conclusion=n < n + 1)

    def p_binomial():
        a, b = pl.symbols("a b", pl.Real)
        return pl.Theorem("b_binomial", [a, b], conclusion=(a - b)**2 == a**2 - 2*a*b + b**2)

    def p_sq_nonneg():
        x = pl.symbol("x", pl.Real)
        return pl.Theorem("b_sq_nonneg", [x], conclusion=pl.Le(0, x**2 + 1))

    def p_trans():
        a, b, c = pl.symbols("a b c", pl.Real)
        return pl.Theorem("b_le_trans", [a, b, c], assumptions={"h1": a <= b, "h2": b <= c},
                          conclusion=a <= c)

    def p_amgm():
        a, b = pl.symbols("a b", pl.Real)
        return pl.Theorem("b_am_gm", [a, b], conclusion=2 * a * b <= a**2 + b**2)

    def p_arith():
        return pl.Theorem("b_arith", [], conclusion=pl.nat(2) + 2 == 4)

    def p_exists():
        z = pl.symbol("z", pl.Int)
        x = pl.symbol("x", pl.Int)
        return pl.Theorem("b_exists_gt", [z], conclusion=pl.Exists([x], x > z))

    def p_exp_pos():
        x = pl.symbol("x", pl.Real)
        return pl.Theorem("b_exp_pos", [x], conclusion=pl.Lt(0, an.exp(x)))

    def p_dist():
        A, B = geo.points("A B")
        return pl.Theorem("b_dist_symm", [A, B], conclusion=geo.dist(A, B) == geo.dist(B, A))

    return [
        Problem("b_imp_self", p_imp, ("logic",), "intro h; exact h"),
        Problem("b_and_comm", p_and_comm, ("logic",), "exact ⟨h.2, h.1⟩"),
        Problem("b_nat_add_zero", p_nat_add_zero, ("nat",), "simp"),
        Problem("b_nat_mul_one", p_nat_mul_one, ("nat",), "simp"),
        Problem("b_nat_lt_succ", p_nat_lt, ("nat",), "omega"),
        Problem("b_binomial", p_binomial, ("algebra",), "ring"),
        Problem("b_sq_nonneg", p_sq_nonneg, ("inequality",), "positivity"),
        Problem("b_le_trans", p_trans, ("inequality",), "linarith"),
        Problem("b_am_gm", p_amgm, ("inequality",), "nlinarith [sq_nonneg (a - b)]"),
        Problem("b_arith", p_arith, ("arith",), "norm_num"),
        Problem("b_exists_gt", p_exists, ("logic", "int"), "use z + 1; omega"),
        Problem("b_exp_pos", p_exp_pos, ("analysis",), "exact Real.exp_pos x"),
        Problem("b_dist_symm", p_dist, ("geometry",), "exact dist_comm A B"),
    ]


BASIC: list[Problem] = []


def basic() -> list[Problem]:
    if not BASIC:
        BASIC.extend(_basic())
    return BASIC


def export_jsonl(path: str | Path, problems: Sequence[Problem] | None = None) -> Path:
    """One JSON object per problem: canonical theorem, Lean statement, tags."""
    from ..render.lean import render_statement

    out = Path(path)
    lines = []
    for p in problems or basic():
        t = p.build()
        lines.append(json.dumps({"name": p.name, "tags": list(p.tags),
                                 "statement": render_statement(t),
                                 "lean": t.to_lean(audit=False),
                                 "theorem": t.canonical()}, ensure_ascii=False))
    out.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    return out


@dataclass
class BenchmarkReport:
    mode: str
    rows: list[dict[str, Any]] = field(default_factory=list)
    seconds: float = 0.0

    @property
    def verified(self) -> int:
        return sum(1 for r in self.rows if r["verified"])

    def summary(self) -> str:
        lines = [f"{r['theorem']:<18} {'VERIFIED' if r['verified'] else r['status']:<10} "
                 f"{' ; '.join(r['script'])}" for r in self.rows]
        lines.append(f"{self.verified}/{len(self.rows)} verified ({self.mode}, "
                     f"{self.seconds:.0f} s)")
        return "\n".join(lines)

    def to_dict(self) -> dict[str, Any]:
        return {"mode": self.mode, "verified": self.verified, "total": len(self.rows),
                "seconds": round(self.seconds, 1), "rows": self.rows}


def run_benchmark(
    proposer: Proposer | None = None,
    problems: Iterable[Problem] | None = None,
    project: LeanProject | str | None = None,
    *,
    mode: str = "session",
    max_depth: int = 4,
    max_expansions: int = 60,
    timeout: float | None = None,
) -> BenchmarkReport:
    """Score a proposer. ``mode="session"`` searches on the REPL; ``mode="batch"`` checks
    the proposer's first-step candidates as whole proofs (no REPL needed)."""
    from ..agent.parse import TacticParser
    from .search import AutomationProposer, search_proof, try_proofs

    proposer = proposer or AutomationProposer()
    report = BenchmarkReport(mode)
    start = time.perf_counter()
    parse = TacticParser(allow_raw=False)
    for p in problems or basic():
        thm = p.build()
        if mode == "session":
            att = search_proof(thm, proposer, project, max_depth=max_depth,
                               max_expansions=max_expansions, verify_timeout=timeout)
        elif mode == "batch":
            obs = {"goals": [f"⊢ {thm.conclusion.to_lean()}"], "theorem": thm.name}
            cands = []
            for c in proposer(obs):
                try:
                    cands.append(c if not isinstance(c, str) else parse(c))
                except Exception:  # noqa: BLE001 - unparseable suggestions are skipped
                    continue
            att = try_proofs(thm, cands, project, timeout=timeout)
        else:
            raise ValueError("mode must be 'session' or 'batch'")
        row = att.to_dict()
        row.pop("result", None)
        row["tags"] = list(p.tags)
        report.rows.append(row)
    report.seconds = time.perf_counter() - start
    return report

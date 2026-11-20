"""Does a certificate found in Python help Lean? Heartbeats with and without it.

Each theorem below has one written step that follows from cited equalities by ring
arithmetic. The same theorems are rendered three times:

* ``rules``: the ordinary alternatives only (Lean searches: linarith, nlinarith, …);
* ``certified``: with :mod:`pyleanx.ring_certificates` (``linear_combination …`` first);
* ``wrong``: with a certifier that always proposes a wrong certificate, which Lean must
  reject while the ordinary alternatives still prove the step.

Lean's work is measured with ``#count_heartbeats in`` (deterministic, unlike wall time on
a loaded machine). Run from the repository root (needs sympy and the lean-project):

    python benchmarks/certificates.py            # writes benchmarks/certificates.json
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
import time
from pathlib import Path

import pyleanx as pl
from pyleanx import justify
from pyleanx.render.lean import render_module

ROOT = Path(__file__).resolve().parents[1]
LEAN_PROJECT = ROOT / "lean-project"
OUT = ROOT / "benchmarks" / "certificates.json"


def suite() -> list[pl.Theorem]:
    x, y, a, b, s, p = pl.symbols("x y a b s p", pl.Real)
    c, e1, e2, e3 = pl.symbols("c e1 e2 e3", pl.Real)
    m, n = pl.symbols("m n", pl.Int)

    def one(name, vs, hyps, goal):  # a theorem whose proof is one cited step
        return pl.Theorem(name, vs, assumptions=hyps, conclusion=goal, proof=pl.proof(
            pl.claim(goal, because=list(hyps), name="h"), pl.conclude(because="h")))

    return [
        one("linear_pair", [x, y], {"h1": x + y == 3, "h2": x - y == 1}, x == 2),
        one("substitute_square", [x, y], {"h1": x == 2, "h2": y == x ** 2}, y == 4),
        one("product_inverse", [x, y], {"h1": x * y == 1, "h2": x == 2}, 2 * y == 1),
        one("int_shift_square", [m, n], {"h": m == n + 1}, m ** 2 == n ** 2 + 2 * n + 1),
        one("power_sum_2", [a, b, s, p], {"hs": a + b == s, "hp": a * b == p},
            a ** 2 + b ** 2 == s ** 2 - 2 * p),
        one("power_sum_3", [a, b, s, p], {"hs": a + b == s, "hp": a * b == p},
            a ** 3 + b ** 3 == s ** 3 - 3 * s * p),
        one("power_sum_4", [a, b, s, p], {"hs": a + b == s, "hp": a * b == p},
            a ** 4 + b ** 4 == s ** 4 - 4 * s ** 2 * p + 2 * p ** 2),
        one("newton_three", [a, b, c, e1, e2, e3],
            {"h1": a + b + c == e1, "h2": a * b + b * c + c * a == e2, "h3": a * b * c == e3},
            a ** 3 + b ** 3 + c ** 3 == e1 ** 3 - 3 * e1 * e2 + 3 * e3),
    ]


def _wrong(goal: justify.Goal) -> str | None:
    # a deliberately wrong certificate: the first cited equality, unscaled
    return f"linear_combination {goal.given[0][0]}" if goal.given else None


def render(variant: str, theorems: list[pl.Theorem]) -> str:
    import pyleanx.ring_certificates as rc

    justify.unregister_certifier(rc.NAME)
    justify.unregister_certifier("wrong")
    if variant == "certified":
        justify.register_certifier(rc.NAME, rc.certify, priority=10, imports=rc.IMPORTS)
    elif variant == "wrong":
        justify.register_certifier("wrong", _wrong, imports=rc.IMPORTS)
    src = render_module(theorems).source
    lines = src.splitlines()
    head = next(i for i, ln in enumerate(lines) if ln.startswith("import "))
    lines.insert(head, "import Mathlib.Util.CountHeartbeats")
    out = []
    for ln in lines:
        # (`#count_heartbeats` lifts the heartbeat limit, so nothing times out here)
        out.append(("#count_heartbeats in\n" + ln) if ln.startswith("theorem ") else ln)
    return "\n".join(out) + "\n"


def run_lean(path: Path) -> tuple[str, float]:
    import os

    from pyleanx.project import find_project

    # the pinned Lean with the Lake environment PyLeanX caches (`lake env` resolves the
    # workspace on every call)
    lake_env = find_project(LEAN_PROJECT).lake_env()
    env = {**os.environ, **lake_env}
    t0 = time.time()
    proc = subprocess.run([lake_env["LEAN"], str(path)], cwd=LEAN_PROJECT, env=env,
                          capture_output=True, text=True, encoding="utf-8", timeout=3600)
    return proc.stdout + proc.stderr, time.time() - t0


def parse(output: str, src: str, theorems: list[pl.Theorem]) -> dict[str, dict]:
    """Per theorem: heartbeats, errors, axioms. Lean prints info messages (heartbeats,
    axioms) without a position, in source order; errors carry ``file:line:col``."""
    starts = sorted((i, m.group(1)) for i, ln in enumerate(src.splitlines(), start=1)
                    if (m := re.match(r"theorem (\w+)", ln)))
    res = {t.name: {"heartbeats": None, "errors": 0, "axioms": None} for t in theorems}
    pending = [name for _, name in starts]      # theorems whose heartbeats come next
    for ln in output.splitlines():
        if (hb := re.match(r"Used (\d+) heartbeats", ln)) and pending:
            res[pending.pop(0)]["heartbeats"] = int(hb.group(1))
        elif (ax := re.match(r"'(\w+)' depends on axioms: \[(.*)\]", ln)) and \
                ax.group(1) in res:
            res[ax.group(1)]["axioms"] = [x.strip() for x in ax.group(2).split(",")]
        elif (ax := re.match(r"'(\w+)' does not depend on any axioms", ln)) and \
                ax.group(1) in res:
            res[ax.group(1)]["axioms"] = []
        elif err := re.search(r":(\d+):\d+: error", ln):
            line = int(err.group(1))
            owner = [name for start, name in starts if start - 1 <= line]
            if owner:
                res[owner[-1]]["errors"] += 1
    return res


def main() -> int:
    theorems = suite()
    build = ROOT / ".pyleanx" / "certificates"
    build.mkdir(parents=True, exist_ok=True)
    report: dict[str, dict] = {}
    reparse = "--reparse" in sys.argv     # read the saved Lean output instead of running Lean
    old = json.loads(OUT.read_text(encoding="utf-8")) if reparse and OUT.exists() else {}
    for variant in ("rules", "certified", "wrong"):
        path = build / f"Certificates_{variant}.lean"
        if reparse:
            src = path.read_text(encoding="utf-8")
            output = (build / f"Certificates_{variant}.out").read_text(encoding="utf-8")
            seconds = old.get(variant, {}).get("seconds", float("nan"))
        else:
            src = render(variant, theorems)
            path.write_text(src, encoding="utf-8", newline="\n")
            output, seconds = run_lean(path)
            (build / f"Certificates_{variant}.out").write_text(output, encoding="utf-8")
        report[variant] = {"seconds": round(seconds, 1), "bytes": len(src.encode()),
                           "theorems": parse(output, src, theorems)}
        print(variant, report[variant]["seconds"], "s", flush=True)
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    std = ["propext", "Classical.choice", "Quot.sound"]
    print(f"{'theorem':20s} {'rules':>12s} {'certified':>12s} {'wrong':>12s}")
    for t in theorems:
        cells = []
        for v in ("rules", "certified", "wrong"):
            r = report[v]["theorems"][t.name]
            ok = r["errors"] == 0 and r["axioms"] is not None and set(r["axioms"]) <= set(std)
            cells.append(f"{r['heartbeats'] if r['heartbeats'] is not None else '-':>9}"
                         f" {'ok' if ok else 'X':>2}")
        print(f"{t.name:20s} " + " ".join(cells))
    return 0


if __name__ == "__main__":
    sys.exit(main())

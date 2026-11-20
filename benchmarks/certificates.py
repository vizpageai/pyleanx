"""Do certificates found in Python help Lean? Proved steps and heartbeats, with and without.

Each theorem below has one written step, from algebra, real inequalities, trigonometry,
logic (existence) and number theory. The same theorems are rendered three times:

* ``rules``: the ordinary alternatives only (Lean searches: linarith, nlinarith, …);
* ``certified``: with :mod:`pyleanx.certifiers` (their certificates first);
* ``wrong``: with a certifier that always proposes a wrong certificate, which Lean must
  reject while the ordinary alternatives still run.

Each theorem is checked under Lean's default budget (``maxHeartbeats 200000``), so a step
the rules cannot prove in time fails, and its work is measured with ``#count_heartbeats``
(deterministic, unlike wall time on a loaded machine). Run from the repository root
(needs sympy and the lean-project):

    python benchmarks/certificates.py            # writes benchmarks/certificates.json
    python benchmarks/certificates.py --reparse  # re-read the saved Lean output
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
from pyleanx import numbers as nt
from pyleanx.render.lean import render_module

ROOT = Path(__file__).resolve().parents[1]
LEAN_PROJECT = ROOT / "lean-project"
OUT = ROOT / "benchmarks" / "certificates.json"


def suite() -> list[tuple[str, pl.Theorem]]:
    """``(domain, theorem)``; every theorem is one cited step."""
    x, y, a, b, s, p = pl.symbols("x y a b s p", pl.Real)
    c, d, e1, e2, e3 = pl.symbols("c d e1 e2 e3", pl.Real)
    m, n = pl.symbols("m n", pl.Int)
    k, j = pl.symbols("k j", pl.Nat)

    def one(name, vs, hyps, goal):
        return pl.Theorem(name, vs, assumptions=hyps, conclusion=goal, proof=pl.proof(
            pl.claim(goal, because=list(hyps), name="h"), pl.conclude(because="h")))

    return [
        ("algebra", one("substitute_square", [x, y], {"h1": x == 2, "h2": y == x ** 2},
                        y == 4)),
        ("algebra", one("power_sum_4", [a, b, s, p], {"hs": a + b == s, "hp": a * b == p},
                        a ** 4 + b ** 4 == s ** 4 - 4 * s ** 2 * p + 2 * p ** 2)),
        ("algebra", one("newton_three", [a, b, c, e1, e2, e3],
                        {"h1": a + b + c == e1, "h2": a * b + b * c + c * a == e2,
                         "h3": a * b * c == e3},
                        a ** 3 + b ** 3 + c ** 3 == e1 ** 3 - 3 * e1 * e2 + 3 * e3)),
        ("algebra", one("nat_square_eq", [k, j], {"h": k == j}, k * k == j * j)),
        ("inequality", one("am_gm_two", [a, b], {}, 2 * a * b <= a ** 2 + b ** 2)),
        ("inequality", one("am_gm_three", [a, b, c],
                           {"ha": a >= 0, "hb": b >= 0, "hc": c >= 0},
                           a ** 3 + b ** 3 + c ** 3 >= 3 * a * b * c)),
        ("inequality", one("cauchy_schwarz_two", [a, b, c, d], {},
                           (a * c + b * d) ** 2 <= (a ** 2 + b ** 2) * (c ** 2 + d ** 2))),
        ("inequality", one("quartic_rearrangement", [x, y], {},
                           x ** 3 * y + x * y ** 3 <= x ** 4 + y ** 4)),
        ("inequality", one("cube_above_one", [x], {"hx": x > 1}, x ** 3 > 1)),
        ("inequality", one("unit_square_product", [a, b],
                           {"h": pl.And(0 <= a, a <= 1, 0 <= b, b <= 1)}, a * b <= 1)),
        ("inequality", one("linear_bound", [x, y], {"h1": x + y <= 4, "h2": y >= 1}, x <= 3)),
        ("analysis", one("sqrt_plus_one", [x], {}, pl.sqrt(x) + 1 > 0)),
        ("trigonometry", one("sin_cos_square", [x],
                             {"h": pl.sin(x) ** 2 + pl.cos(x) ** 2 == 1},
                             (pl.sin(x) + pl.cos(x)) ** 2 == 1 + 2 * pl.sin(x) * pl.cos(x))),
        ("trigonometry", one("sin_square_le_one", [x],
                             {"h": pl.sin(x) ** 2 + pl.cos(x) ** 2 == 1},
                             pl.sin(x) ** 2 <= 1)),
        ("logic", one("exists_root", [], {},
                      pl.Exists(y, pl.And(y ** 2 + 2 * y == 3, y > 0)))),
        ("logic", one("exists_larger", [x], {}, pl.Exists(y, y > x))),
        ("logic", one("exists_complement", [x], {}, pl.Exists(y, x + y == 3))),
        ("number theory", one("difference_divides_cubes", [m, n], {},
                              nt.divides(m - n, m ** 3 - n ** 3))),
        ("number theory", one("divides_combination", [m, n], {"h": nt.divides(m, n)},
                              nt.divides(m, 2 * n + 3 * n * n))),
        ("number theory", one("nat_divides_square_plus", [k], {}, nt.divides(k, k ** 2 + k))),
    ]


def _wrong(goal: justify.Goal) -> str | None:
    # a deliberately wrong certificate
    return f"linear_combination {goal.given[0][0]}" if goal.given else "exact absurd"


def render(variant: str, theorems: list[pl.Theorem]) -> str:
    import pyleanx.certifiers as certs

    certs.disable()
    justify.unregister_certifier("wrong")
    if variant == "certified":
        certs.enable()
    elif variant == "wrong":
        justify.register_certifier("wrong", _wrong, imports=certs.IMPORTS)
    src = render_module(theorems).source
    lines = src.splitlines()
    first_import = next(i for i, ln in enumerate(lines) if ln.startswith("import "))
    lines.insert(first_import, "import Mathlib.Util.CountHeartbeats")
    out = []
    for ln in lines:
        if ln.startswith("theorem "):
            # count the work; check under the default budget
            out += ["#count_heartbeats in", "set_option maxHeartbeats 200000 in"]
        out.append(ln)
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
            owner = [name for start, name in starts if start - 2 <= line]
            if owner:
                res[owner[-1]]["errors"] += 1
    return res


def main() -> int:
    domains = suite()
    theorems = [t for _, t in domains]
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
    print(f"{'domain':14s} {'theorem':26s} {'rules':>12s} {'certified':>12s} {'wrong':>12s}")
    for domain, t in domains:
        cells = []
        for v in ("rules", "certified", "wrong"):
            r = report[v]["theorems"][t.name]
            ok = r["errors"] == 0 and r["axioms"] is not None and set(r["axioms"]) <= set(std)
            cells.append(f"{r['heartbeats'] if r['heartbeats'] is not None else '-':>9}"
                         f" {'ok' if ok else 'X':>2}")
        print(f"{domain:14s} {t.name:26s} " + " ".join(cells))
    return 0


if __name__ == "__main__":
    sys.exit(main())

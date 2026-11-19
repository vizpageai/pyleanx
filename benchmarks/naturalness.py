"""How natural are PyLeanX written proofs? A benchmark over the textbook examples.

    python benchmarks/naturalness.py            # static measures, writes docs/benchmark.md
    python benchmarks/naturalness.py --lean     # also checks every proof in the Lean REPL
    python benchmarks/naturalness.py --lean --only euclid_book1,cz_intervals

Lean results are saved per proof in ``benchmarks/lean_results.json`` with a fingerprint of
the proof's Lean source; a result for an older source is reported as stale.

For every written proof in the examples it counts

* steps: claims, choices, cases, chains ... (nested steps included);
* bookkeeping steps: steps a textbook would leave implicit -- distinctness (A ≠ B),
  positivity (x > 0, |AB| > 0), notation (|BA| = |AB|, ∠ABC = ∠CBA, "BAC is a triangle"),
  and measure-theoretic side conditions (measurable, integrable, finite measure, a.e.);
* library facts cited (by name or by description) and ``similarly`` steps;
* raw Lean (``pl.raw_tactic``) -- should be zero;

and, with ``--lean``, whether the proof passes Lean as written (first try).
The bookkeeping classification is a heuristic on the shape of each step's statement.
"""

from __future__ import annotations

import contextlib
import importlib
import io
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "examples"))

import pyleanx as pl  # noqa: E402
from pyleanx.expr import App, Compare, Lit, NotP  # noqa: E402
from pyleanx.proofs import CaseSplit, Chain, Choose, Claim, Conclude, contains_raw  # noqa: E402
from pyleanx.terms import Apply, Const  # noqa: E402
from pyleanx.theorem import Theorem  # noqa: E402

#: (area, example module); modules with ``all_solutions()`` contribute their solutions
SOURCES = [
    ("geometry", "pythagoras_similar"), ("geometry", "euclid_book1"),
    ("geometry", "readable_side_splitter"), ("geometry", "readable_angle_bisector"),
    ("geometry", "textbook_geometry"),
    ("algebra & number theory", "readable_am_gm"),
    ("algebra & number theory", "readable_bernoulli"),
    ("algebra & number theory", "readable_odd_sum"),
    ("algebra & number theory", "readable_consecutive_even"),
    ("algebra & number theory", "readable_group_abelian"),
    ("algebra & number theory", "readable_infinite_primes"),
    ("analysis", "readable_limit_sum"), ("analysis", "readable_trig"),
    ("analysis", "readable_cauchy_integral"), ("analysis", "using_cauchy_integral"),
    ("analysis", "analysis_lecture"),
    ("harmonic analysis", "harmonic_lecture"), ("harmonic analysis", "singular_integrals"),
    ("harmonic analysis", "marcinkiewicz"), ("harmonic analysis", "calderon_zygmund"),
    ("harmonic analysis", "cz_intervals"), ("harmonic analysis", "hilbert_kernel"),
    ("harmonic analysis", "hilbert_transform"),
]

_SIDE = ("MeasurableSet", "Measurable", "MeasureTheory.Integrable", "MeasureTheory.IntegrableOn",
         "MeasureTheory.LocallyIntegrable", "AEMeasurable", "MeasureTheory.AEStronglyMeasurable",
         "Filter.EventuallyLE", "IntervalIntegrable", "Set.Nonempty", "BddAbove", "BddBelow",
         "IsClosed", "IsCompact")


def _is_zero(e: object) -> bool:
    return isinstance(e, Lit) and e.value == 0


def _head(e: object) -> str:
    if isinstance(e, Apply) and isinstance(e.fn, Const):
        return e.fn.name
    if isinstance(e, App):
        return e.func.lean_name
    return ""


def _same_up_to_notation(a: object, b: object) -> bool:
    """|AB| vs |BA|, ∠ABC vs ∠CBA."""
    if not (isinstance(a, App) and isinstance(b, App) and _head(a) == _head(b)):
        return False
    xs, ys = [x._key() for x in a.args], [y._key() for y in b.args]
    if _head(a) == "dist":
        return sorted(map(repr, xs)) == sorted(map(repr, ys))
    if _head(a) == "EuclideanGeometry.angle":
        return xs[1] == ys[1] and {repr(xs[0]), repr(xs[2])} == {repr(ys[0]), repr(ys[2])}
    return False


def bookkeeping_kind(prop: object, hyps: list[object]) -> str:
    """'' for mathematics, else the kind of bookkeeping the step is."""
    if isinstance(prop, Compare):
        if prop.op == "ne":
            return "distinctness"
        if prop.op in ("gt", "ge", "lt", "le") and (_is_zero(prop.lhs) or _is_zero(prop.rhs)):
            return "positivity"
        if prop.op == "eq" and _same_up_to_notation(prop.lhs, prop.rhs):
            return "notation"
        if prop.op == "lt" and "finite" not in repr(prop) and "Top.top" in repr(prop):
            return "side condition"
    if isinstance(prop, NotP) and _head(prop.arg) == "Collinear":
        if any(isinstance(h, NotP) and _head(h.arg) == "Collinear" for h in hyps):
            return "notation"
    if _head(prop) in _SIDE:
        return "side condition"
    return ""


@dataclass
class Row:
    area: str
    module: str
    theorem: str
    steps: int
    bookkeeping: dict[str, int]
    described: int
    similarly: int
    raw: bool
    lean: str = ""

    @property
    def bk(self) -> int:
        return sum(self.bookkeeping.values())


def _walk(t: object, hyps: list[object], row: Row) -> None:
    from pyleanx.proofs import Steps

    if t is None:
        return
    items = t.tactics if isinstance(t, Steps) else (t,)
    for s in items:
        if isinstance(s, Steps):
            _walk(s, hyps, row)
            continue
        if isinstance(s, Conclude):
            row.described += sum(1 for f in s.facts if _described(f))
            _walk(s.proof, hyps, row)
            continue
        row.steps += 1
        if isinstance(s, Claim):
            kind = bookkeeping_kind(s.prop, hyps)
            if kind:
                row.bookkeeping[kind] = row.bookkeeping.get(kind, 0) + 1
            row.described += sum(1 for f in s.facts if _described(f))
            if s.note.startswith("similarly"):
                row.similarly += 1
            _walk(s.proof, hyps, row)
        elif isinstance(s, CaseSplit):
            for c in s.cases:
                _walk(c.body, hyps, row)
        elif isinstance(s, (Choose, Chain)):
            row.described += sum(1 for f in getattr(s, "facts", ()) if _described(f))
        for sub in s.sub_tactics():
            if not isinstance(s, (Claim, CaseSplit)):
                _walk(sub, hyps, row)


def _described(f: object) -> bool:
    # a fact cited by description is a library Name with a label (not a hypothesis name)
    return bool(getattr(f, "label", "")) and "." in getattr(f, "name", "")


def collect() -> list[tuple[str, str, Theorem]]:
    out: list[tuple[str, str, Theorem]] = []
    seen: set[str] = set()
    for area, mod_name in SOURCES:
        with contextlib.redirect_stdout(io.StringIO()):
            mod = importlib.import_module(mod_name)
        thms = list(getattr(mod, "THEOREMS", [])) or [
            v for v in vars(mod).values() if isinstance(v, Theorem)]
        if hasattr(mod, "all_solutions"):
            with contextlib.redirect_stdout(io.StringIO()):
                thms += list(mod.all_solutions())
        for t in thms:
            if t.proof is None or t.name in seen:
                continue
            seen.add(t.name)
            out.append((area, mod_name, t))
    return out


#: proofs Lean did not accept in this run: (module, theorem, why)
FAILED: list[tuple[str, str, str]] = []


def _annotate(title: str, message: str) -> None:
    """On GitHub Actions, report a failure as an annotation (readable without the logs)."""
    import os

    if os.environ.get("GITHUB_ACTIONS") != "true":
        return

    def esc(s: str) -> str:
        return s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")

    title = esc(title).replace(",", "%2C").replace(":", "%3A")
    print(f"::error title={title}::{esc(message)}", flush=True)


def measure(lean: bool = False, only: set[str] | None = None) -> list[Row]:
    rows = []
    items = collect()
    for area, mod_name, t in items:
        row = Row(area, mod_name, t.name, 0, {}, 0, 0, contains_raw(t.proof))
        _walk(t.proof, [h.prop for h in t.assumptions], row)
        rows.append(row)
    saved = _load_results()
    if lean:
        from pyleanx.backend import repl_check

        repl_check.MAX_IMPORT_SETS = 1  # one environment at a time: memory, not speed
        by_mod: dict[str, list[int]] = {}
        for i, (_, m, _) in enumerate(items):
            if only is None or m in only:
                by_mod.setdefault(m, []).append(i)
        for m, idx in by_mod.items():
            print(f"checking {m} ({len(idx)} proofs) ...", file=sys.stderr, flush=True)
            res = pl.check_all([items[i][2] for i in idx], timeout=3600)
            for i, r in zip(idx, res, strict=True):
                why = "; ".join(d.message.splitlines()[0][:160] for d in r.errors[:2])
                saved[items[i][2].name] = {"status": "pass" if r.verified else r.status.value,
                                           "fingerprint": _fp(items[i][2]), "why": why}
                if not r.verified:
                    FAILED.append((m, items[i][2].name, why))
                    _annotate(f"{m}.{items[i][2].name}", f"{r.status.value}: {why}")
            _save_results(saved)  # after every module: a stopped run keeps what it checked
    for (_, _, t), row in zip(items, rows, strict=True):
        got = saved.get(t.name)
        if got is not None:
            # a result for an older version of the proof is shown as stale
            row.lean = got["status"] if got.get("fingerprint") == _fp(t) else "stale"
    return rows


RESULTS = ROOT / "benchmarks" / "lean_results.json"


def _fp(t: Theorem) -> str:
    """The proof's identity: its Lean source (so engine changes make results stale)."""
    import hashlib

    return hashlib.sha256(t.to_lean().encode()).hexdigest()[:16]


def _load_results() -> dict:
    import json

    try:
        return json.loads(RESULTS.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def _save_results(data: dict) -> None:
    import json

    text = json.dumps(data, indent=1, sort_keys=True, ensure_ascii=False)
    RESULTS.write_text(text + "\n", encoding="utf-8", newline="\n")


def report(rows: list[Row]) -> str:
    n = len(rows)
    steps = sum(r.steps for r in rows)
    bk = sum(r.bk for r in rows)
    kinds: dict[str, int] = {}
    for r in rows:
        for k, v in r.bookkeeping.items():
            kinds[k] = kinds.get(k, 0) + v
    lines = ["# Naturalness benchmark", "",
             "Generated by `python benchmarks/naturalness.py` over the written proofs in "
             "`examples/`. Bookkeeping = steps a textbook leaves implicit (heuristic).", "",
             f"- proofs: **{n}**, steps: **{steps}** (mean {steps / max(n, 1):.1f} per proof)",
             f"- bookkeeping steps: **{bk}** ({100 * bk / max(steps, 1):.0f}% of all steps): "
             + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())),
             f"- library facts cited: {sum(r.described for r in rows)}; "
             f"`similarly` steps: {sum(r.similarly for r in rows)}; "
             f"proofs with raw Lean: {sum(r.raw for r in rows)}"]
    if any(r.lean for r in rows):
        passed = sum(r.lean == "pass" for r in rows)
        stale = sum(r.lean == "stale" for r in rows)
        failed = sum(r.lean not in ("", "pass", "stale") for r in rows)
        unchecked = sum(not r.lean for r in rows)
        lines.append(f"- pass Lean as written: **{passed}/{n}**; failed: {failed}; checked only "
                     f"with an earlier version of the generated Lean (stale): {stale}; not yet "
                     f"checked: {unchecked}")
    lines += ["", "| area | example | theorem | steps | bookkeeping | facts cited | Lean |",
              "|---|---|---|---:|---:|---:|---|"]
    for r in rows:
        bk_s = f"{r.bk}" + (f" ({', '.join(f'{k} {v}' for k, v in r.bookkeeping.items())})"
                            if r.bk else "")
        lines.append(f"| {r.area} | {r.module} | `{r.theorem}` | {r.steps} | {bk_s} | "
                     f"{r.described} | {r.lean or '–'} |")
    by_area: dict[str, list[Row]] = {}
    for r in rows:
        by_area.setdefault(r.area, []).append(r)
    lines += ["", "| area | proofs | mean steps | bookkeeping share |", "|---|---:|---:|---:|"]
    for a, rs in by_area.items():
        st = sum(r.steps for r in rs)
        lines.append(f"| {a} | {len(rs)} | {st / len(rs):.1f} | "
                     f"{100 * sum(r.bk for r in rs) / max(st, 1):.0f}% |")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    only = None
    if "--only" in sys.argv:
        only = set(sys.argv[sys.argv.index("--only") + 1].split(","))
    if "--list" in sys.argv:
        print(" ".join(dict.fromkeys(m for _, m in SOURCES)))
        raise SystemExit(0)
    rows = measure(lean="--lean" in sys.argv, only=only)
    text = report(rows)
    out = ROOT / "docs" / "benchmark.md"
    out.write_text(text, encoding="utf-8", newline="\n")
    print(text)
    if FAILED:  # with --lean: a proof Lean rejects fails the run (CI gate)
        print(f"{len(FAILED)} proof(s) not accepted by Lean:", file=sys.stderr)
        for m, name, why in FAILED:
            print(f"  {m}.{name}: {why}", file=sys.stderr)
        raise SystemExit(1)

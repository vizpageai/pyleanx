"""Find a fact by what it says: cite "AA similarity" instead of ``geo.similar_AA``.

    pl.claim(geo.similar(...), because="AA similarity")
    pl.claim(AB == AD + DB, because=["segment addition", "hD"])
    pl.search_facts("similar triangles proportional sides")   # ranked candidates
    pl.fact("the angles of a triangle add up to 180°")         # the Name, or an error

A string in ``because=`` that contains a space is a *description* (hypothesis and step
names never contain spaces). It is matched against the words of every fact the domain
modules provide (geometry, real-variable methods, analysis, algebra, number theory,
complex analysis, harmonic analysis, the Hilbert transform): their printed labels and
their Python names. The best match is used when it is clearly the best; otherwise the
step is rejected with the candidates, so a description never silently picks a fact.
Lean still checks that the chosen fact justifies the step.
"""

from __future__ import annotations

import importlib
import math
import re
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache

from .errors import TacticError

#: (module, prefix used when printing a candidate)
_DOMAINS = (("geometry", "geo"), ("realvar", "rv"), ("analysis", "an"), ("algebra", "alg"),
            ("numbers", "nt"), ("complex_analysis", "ca"), ("harmonic", "ha"),
            ("hilbert", "hil"))

_STOP = {"a", "an", "the", "of", "is", "are", "and", "or", "to", "in", "on", "for", "by",
         "with", "its", "it", "be", "as", "at", "that", "this", "when", "if", "then", "from",
         "so", "gives", "give", "has", "have", "any", "every", "all", "two", "one"}
_SYN = {"triangles": "triangle", "angles": "angle", "sides": "side", "lines": "line",
        "similarity": "similar", "proportional": "proportion", "proportion": "proportion",
        "perpendicular": "perp", "⊥": "perp", "∥": "parallel", "parallels": "parallel",
        "180°": "pi", "180": "pi", "π": "pi", "sum": "add", "adds": "add", "add": "add",
        "addition": "add", "subtraction": "sub", "equal": "eq", "equals": "eq",
        "integrals": "integral", "integrable": "integrable", "functions": "function",
        "measures": "measure", "sets": "set", "points": "point", "vertices": "vertex",
        "segments": "segment", "circles": "circle", "squares": "square", "squared": "square"}


def _words(text: str) -> list[str]:
    raw = re.findall(r"[A-Za-z0-9°π⊥∥]+", text.lower().replace("_", " "))
    out = []
    for w in raw:
        w = _SYN.get(w, w)
        if len(w) > 4 and w.endswith("s") and not w.endswith("ss"):
            w = w[:-1]
        if w not in _STOP:
            out.append(w)
    return out


@dataclass(frozen=True)
class FactEntry:
    qualified: str   # e.g. "geo.similar_AA"
    obj: object      # the Name / LibraryFact
    label: str
    words: tuple[str, ...]


@lru_cache(maxsize=1)
def _catalog() -> tuple[FactEntry, ...]:
    out: list[FactEntry] = []
    seen: set[str] = set()
    for mod_name, prefix in _DOMAINS:
        try:
            mod = importlib.import_module(f"pyleanx.{mod_name}")
        except Exception:  # noqa: BLE001 - an optional domain must not break search
            continue
        for py_name, obj in getattr(mod, "LEMMAS", {}).items():
            if f"{prefix}.{py_name}" in seen:
                continue
            seen.add(f"{prefix}.{py_name}")
            label = getattr(obj, "label", "") or ""
            words = tuple(_words(label) * 2 + _words(py_name))
            out.append(FactEntry(f"{prefix}.{py_name}", obj, label, words))
    return tuple(out)


@lru_cache(maxsize=1)
def _idf() -> dict[str, float]:
    cat = _catalog()
    df: Counter[str] = Counter()
    for e in cat:
        df.update(set(e.words))
    n = max(1, len(cat))
    return {w: math.log(1 + n / c) for w, c in df.items()}


def search_facts(query: str, k: int = 5) -> list[tuple[float, str, str]]:
    """Ranked ``(score, name, label)`` of the facts best matching ``query``."""
    q = _words(query)
    if not q:
        return []
    idf = _idf()
    scored = []
    for e in _catalog():
        ws = Counter(e.words)
        s = sum(idf.get(w, 0.0) * min(ws[w], 2) for w in set(q) if w in ws)
        if s > 0:
            # prefer facts that are about little else
            s /= math.sqrt(1 + len(set(e.words) - set(q)) / 4)
            scored.append((round(s, 3), e.qualified, e.label))
    scored.sort(key=lambda t: (-t[0], t[1]))
    return scored[:k]


def _norm(text: str) -> str:
    return " ".join(re.findall(r"[a-z0-9°π]+", text.lower().replace("_", " ")))


def facts_for(query: str) -> list[object]:
    """The facts ``query`` describes, for ``because=``.

    * exactly a fact's printed label (character for character, ignoring case) or its Python
      name: that fact -- or, when several facts share the label (a family such as the six
      parts of "CPCTC"), all of them, and Lean uses whichever justifies the step;
    * otherwise the best match by words, if it is clearly the best;
    * otherwise an error listing the candidates.
    """
    raw = query.strip().casefold()
    by_name: dict[str, FactEntry] = {}
    for e in _catalog():
        if raw and (raw == e.label.strip().casefold()
                    or raw == e.qualified.split(".", 1)[1].casefold()):
            by_name.setdefault(str(getattr(e.obj, "name", e.qualified)), e)
    if by_name:
        return [e.obj for e in by_name.values()]
    return [fact(query)]


def fact(query: str) -> object:
    """The fact ``query`` describes; an error listing candidates if it is unclear.

    A query that is exactly a fact's printed label, or its Python name (``straight
    angle`` for ``geo.straight_angle``), selects that fact.
    """
    raw = query.strip().casefold()
    exact_raw = {str(getattr(e.obj, "name", e.qualified)): e for e in _catalog()
                 if raw and raw == e.label.strip().casefold()}
    if len(exact_raw) == 1:
        return next(iter(exact_raw.values())).obj
    q = _norm(query)
    exact = {getattr(e.obj, "name", e.qualified): e for e in _catalog()
             if q and (q == _norm(e.label) or q == _norm(e.qualified.split(".", 1)[1]))}
    if len(exact) == 1:
        return next(iter(exact.values())).obj
    hits = search_facts(query, k=4)
    if not hits:
        raise TacticError(f"no fact matches “{query}”; use pl.search_facts to browse")
    by_q = {e.qualified: e for e in _catalog()}
    # aliases of one Lean declaration are one candidate
    distinct: list[tuple[float, str, str]] = []
    names: set[str] = set()
    for h in hits:
        lean_name = getattr(by_q[h[1]].obj, "name", h[1])
        if lean_name not in names:
            names.add(lean_name)
            distinct.append(h)
    hits = distinct
    best = hits[0]
    clear = len(hits) == 1 or best[0] >= 1.25 * hits[1][0]
    if not clear:
        cands = "; ".join(f"{n} ({lab})" if lab else n for _, n, lab in hits)
        raise TacticError(f"“{query}” could mean several facts: {cands}. Cite one by name "
                          "or describe it more precisely")
    return by_q[best[1]].obj


__all__ = ["fact", "facts_for", "search_facts"]

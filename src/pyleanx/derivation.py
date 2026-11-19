"""The derivation graph of a written proof: its steps and what each depends on.

PyTorch's autograd records every operation as it runs; ``backward()`` then walks that
record. A written proof is recorded the same way: each hypothesis and each step becomes a
:class:`Node` with its statement, the names it cites, the library facts it uses and the
names in scope when Lean checks it (the local context of its ``have``). Scope checks,
explanations and error attribution read this graph instead of re-walking the proof.

    d = thm.derivation()            # or pl.derivation(thm)
    d["h2"].cites                   # ('h1', 'hD')
    d.depends_on("h2")              # every node h2 rests on, transitively
    d.introduced                    # every name the proof introduces

Edges are *citations*. In a written proof, earlier steps and hypotheses are available to
every later step even when not cited (Lean's local context), so a citation is the
author's account of a dependency, not a proof that nothing else was used; ``scope`` lists
what was available.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator
from dataclasses import dataclass
from typing import Any

from .proofs import (
    Branches,
    Cases,
    CaseSplit,
    Chain,
    Choose,
    Claim,
    Conclude,
    Fix,
    Have,
    Induction,
    InductionOn,
    Intro,
    Let,
    Name,
    Obtain,
    Steps,
    Suffices,
    SupposeNot,
    Tactic,
    Take,
)


@dataclass(frozen=True)
class Node:
    """One hypothesis or step."""

    name: str                       # its name in Lean ("hx", "step3"); "" for anonymous
    kind: str                       # hypothesis | claim | chain | choose | fix | let | …
    statement: Any = None           # the Expr it states (None if it states nothing)
    cites: tuple[str, ...] = ()     # names of hypotheses/steps it cites
    facts: tuple[str, ...] = ()     # library facts and theorems it cites (Lean names)
    scope: tuple[str, ...] = ()     # names in Lean's local context when it is checked
    introduces: tuple[str, ...] = ()  # names it adds to the context of later steps
    tactic: Tactic | None = None    # the proof step itself (None for hypotheses)


@dataclass(frozen=True)
class Derivation:
    theorem: str
    nodes: tuple[Node, ...]

    def __iter__(self) -> Iterator[Node]:
        return iter(self.nodes)

    def __len__(self) -> int:
        return len(self.nodes)

    def __getitem__(self, name: str) -> Node:
        for n in self.nodes:
            if n.name == name or name in n.introduces:
                return n
        raise KeyError(f"{self.theorem}: no hypothesis or step called {name!r}")

    @property
    def introduced(self) -> frozenset[str]:
        """Every name a hypothesis or step introduces (in any scope)."""
        return frozenset(x for n in self.nodes for x in n.introduces)

    def depends_on(self, name: str) -> tuple[str, ...]:
        """The names ``name`` rests on through citations, transitively, in proof order."""
        seen: list[str] = []
        todo = list(self[name].cites)
        while todo:
            c = todo.pop()
            if c in seen:
                continue
            seen.append(c)
            try:
                todo.extend(self[c].cites)
            except KeyError:
                continue
        order = {x: (i, j) for i, n in enumerate(self.nodes)
                 for j, x in enumerate(n.introduces)}
        return tuple(sorted(seen, key=lambda x: order.get(x, (len(self.nodes), 0))))

    def cited_by(self, name: str) -> tuple[str, ...]:
        """The steps that cite ``name`` directly."""
        return tuple(n.name for n in self.nodes if name in n.cites)

    def _rows(self) -> list[tuple[str, str, str, str, str]]:
        from .prose import plain

        rows = []
        for n in self.nodes:
            stmt = ""
            try:
                if n.statement is not None:
                    stmt = plain(n.statement)
                elif isinstance(n.tactic, Chain) and n.tactic.links:
                    # a chain states its first term related to its last
                    stmt = f"{plain(n.tactic.first)} … {plain(n.tactic.links[-1][1])}"
            except Exception:  # noqa: BLE001 - display only
                stmt = str(n.statement or "")
            facts = ", ".join(f.split(".")[-1] for f in n.facts)
            rows.append((", ".join(n.introduces) or "–", n.kind, stmt,
                         ", ".join(n.cites), facts))
        return rows

    def __str__(self) -> str:
        lines = [f"Derivation of {self.theorem}:"]
        for intro, kind, stmt, cites, facts in self._rows():
            why = "; ".join(x for x in (cites and f"cites {cites}", facts and f"by {facts}") if x)
            lines.append(f"  {intro:12s} {kind:11s} {stmt}" + (f"   ({why})" if why else ""))
        return "\n".join(lines)

    def _repr_markdown_(self) -> str:  # Jupyter
        out = [f"**Derivation of `{self.theorem}`**", "",
               "| name | kind | statement | cites | facts |", "|---|---|---|---|---|"]
        for row in self._rows():
            out.append("| " + " | ".join(c.replace("|", "\\|") for c in row) + " |")
        return "\n".join(out)


def _cited(facts: Iterable[Any], known: Iterable[str]) -> tuple[tuple[str, ...], tuple[str, ...]]:
    """Split cited terms into names of the proof's own hypotheses/steps, and library facts."""
    known = set(known)
    own: list[str] = []
    lib: list[str] = []
    for f in facts:
        name = f.name if isinstance(f, Name) else getattr(f, "name", None)
        if not isinstance(name, str):
            continue
        (own if name in known else lib).append(name)
    return tuple(dict.fromkeys(own)), tuple(dict.fromkeys(lib))


def _walk(t: Tactic | None, scope: tuple[str, ...], every: set[str],
          out: list[Node]) -> tuple[str, ...]:
    """Append the nodes of ``t``; return the scope after it."""
    if t is None:
        return scope
    after = _node(t, scope, every, out)
    if not isinstance(t, (Steps, Branches, Claim, Conclude, CaseSplit, InductionOn)):
        for sub in t.sub_tactics():  # sub-proofs of any other move (have, take, …)
            _walk(sub, scope, every, out)
    return after


def _node(t: Tactic | None, scope: tuple[str, ...], every: set[str],
          out: list[Node]) -> tuple[str, ...]:
    if t is None:
        return scope
    if isinstance(t, Steps):
        for s in t.tactics:
            scope = _walk(s, scope, every, out)
        return scope
    if isinstance(t, Branches):
        for b in t.branches:
            _walk(b, scope, every, out)
        return scope

    def add(kind: str, name: str = "", statement: Any = None, facts: Iterable[Any] = (),
            introduces: Iterable[str] = ()) -> tuple[str, ...]:
        own, lib = _cited(facts, every)
        intro = tuple(x for x in introduces if x)
        out.append(Node(name, kind, statement, own, lib, scope, intro, t))
        return (*scope, *intro)

    if isinstance(t, Claim):
        new = add("claim", t.name, t.prop, t.facts, (t.name,))
        if t.proof is not None:
            _walk(t.proof, scope, every, out)
        return new
    if isinstance(t, Chain):
        facts = [f for _, _, fs, _ in t.links for f in fs]
        return add("chain", t.name, None, facts, (t.name,))
    if isinstance(t, Choose):
        return add("choose", t.names[0] if t.names else "", t.prop, t.facts, t.names)
    if isinstance(t, Fix):
        return add("fix", "", None, (), tuple(n for n, _ in t.hyps))
    if isinstance(t, Let):
        return add("let", t.eq_name, None, (), (t.eq_name,))
    if isinstance(t, Take):
        return add("take", "", t.such_that, t.facts)
    if isinstance(t, Suffices):
        return add("suffices", t.name, t.prop, t.facts, (t.name,))
    if isinstance(t, SupposeNot):
        return add("suppose_not", t.name, t.prop, (), (t.name,))
    if isinstance(t, CaseSplit):
        new = add("cases", t.name, None, t.facts, (t.name,))
        for c in t.cases:
            out.append(Node(c.name, "case", c.prop, (), (), new, (c.name,), None))
            _walk(c.body, (*new, c.name), every, out)
        return new
    if isinstance(t, InductionOn):
        new = add("induction", "", None)
        _walk(t.base, new, every, out)
        out.append(Node(t.ih, "induction_hypothesis", None, (), (), new, (t.ih,), None))
        _walk(t.step, (*new, t.ih), every, out)
        return new
    if isinstance(t, Conclude):
        new = add("conclusion", "", None, t.facts)
        if t.proof is not None:
            _walk(t.proof, scope, every, out)
        return new
    if isinstance(t, Have):
        return add("have", t.name, t.prop, (), (t.name,))
    if isinstance(t, (Intro, Obtain, Cases)):
        names = list(getattr(t, "names", ()) or ())
        for alt in getattr(t, "alternatives", ()) or ():
            names.extend(alt)
        return add(type(t).__name__.lower(), "", None, (), names)
    if isinstance(t, Induction):
        return add("induction", "", None, (), (t.var, *t.succ_names))
    return add(type(t).__name__.lower())


def _all_names(t: Tactic | None) -> set[str]:
    """Names introduced anywhere in ``t`` (a first pass, so citations can be classified)."""
    out: list[Node] = []
    _walk(t, (), set(), out)
    return {x for n in out for x in n.introduces}


def derivation(thm: Any) -> Derivation:
    """The derivation graph of a theorem's (prepared) proof."""
    hyps = [h.name for h in thm.assumptions]
    every = set(hyps) | _all_names(thm.proof) | {"this"}
    nodes = [Node(h.name, "hypothesis", h.prop, (), (), (), (h.name,), None)
             for h in thm.assumptions]
    out: list[Node] = []
    _walk(thm.proof, tuple(hyps), every, out)
    return Derivation(thm.name, (*nodes, *out))


__all__ = ["Derivation", "Node", "derivation"]

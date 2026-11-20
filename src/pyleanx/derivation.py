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
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

from .proofs import (
    Auto,
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
    #: what each introduced name states, when a step introduces several (fix, choose)
    states: tuple[tuple[str, Any], ...] = ()


@dataclass(frozen=True)
class Derivation:
    theorem: str
    nodes: tuple[Node, ...]
    #: id(step) -> the goal it proves, where known (the theorem's conclusion, a claim's
    #: statement, … carried through the steps; see _track_goals); ("ih", id(induction))
    #: -> the statement of its induction hypothesis
    goals: dict[Any, Any] = field(default_factory=dict, compare=False, repr=False)

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

    def scope_statements(self, node: Node) -> dict[str, Any]:
        """Lean name -> statement of what is in scope at ``node`` (the latest earlier
        hypothesis or step of that name; names that state several things are left out)."""
        out: dict[str, Any] = {}
        for n in self.nodes:
            if n is node:
                break
            stmt = _statement(n)
            if n.kind == "induction_hypothesis":
                stmt = self.goals.get(("ih", id(n.tactic)))
            states = dict(n.states)
            for x in n.introduces:
                if x in node.scope:
                    if x in states:
                        out[x] = states[x]
                    elif stmt is not None and len(n.introduces) == 1:
                        out[x] = stmt
                    else:
                        out.pop(x, None)
        return out

    def certificates(self, name: str) -> list[tuple[str, str]]:
        """``(certifier, tactic)`` the registered certifiers propose for the step ``name``
        (see :func:`pyleanx.justify.register_certifier`); Lean checks whichever is used."""
        from .justify import certificates
        from .render.lean import render_term

        n = self[name]
        stmt = _statement(n)
        if stmt is None:
            return []
        facts = getattr(n.tactic, "facts", ()) or ()
        return certificates(stmt, [render_term(t) for t in facts], self.scope_statements(n))

    def goal(self, node: Node) -> Any:
        """The statement ``node`` proves, where known."""
        stmt = _statement(node)
        if stmt is not None and isinstance(node.tactic, (Claim, Chain)):
            return stmt
        return self.goals.get(id(node.tactic))

    def contexts(self) -> dict[int, Any]:
        """``id(step) -> StepContext(goal, scope statements)`` for the steps certifiers can
        help (claims, chains, conclusions, ``auto``), used while the proof is rendered."""
        from .justify import StepContext

        return {id(n.tactic): StepContext(self.goal(n), tuple(self.scope_statements(n).items()))
                for n in self.nodes if isinstance(n.tactic, (Claim, Chain, Conclude, Auto))}

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


def _statement(n: Node) -> Any:
    if n.statement is not None:
        return n.statement
    if isinstance(n.tactic, Chain) and n.tactic.links:
        return n.tactic.statement()
    return None


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
            introduces: Iterable[str] = (),
            states: tuple[tuple[str, Any], ...] = ()) -> tuple[str, ...]:
        own, lib = _cited(facts, every)
        intro = tuple(x for x in introduces if x)
        out.append(Node(name, kind, statement, own, lib, scope, intro, t, states))
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
        return add("choose", t.names[0] if t.names else "", t.prop, t.facts, t.names,
                   _split_names(t.names, t.prop))
    if isinstance(t, Fix):
        return add("fix", "", None, (), tuple(n for n, _ in t.hyps), tuple(t.hyps))
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
        out.append(Node(t.ih, "induction_hypothesis", None, (), (), new, (t.ih,), t))
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


def _track_goals(t: Tactic | None, goal: Any, out: dict[int, Any]) -> Any:
    """Record the goal of every step under ``t``; return the goal after ``t``.

    Steps that keep the goal (claims, chains, choices, definitions) pass it on; a step that
    changes it in a way not tracked here (intro, cases, induction, …) leaves it unknown.
    """
    if t is None:
        return goal
    if goal is not None:
        out[id(t)] = goal
    if isinstance(t, Steps):
        for s in t.tactics:
            goal = _track_goals(s, goal, out)
        return goal
    if isinstance(t, Claim):
        _track_goals(t.proof, t.prop, out)
        return goal
    if isinstance(t, Conclude):
        _track_goals(t.proof, goal, out)
        return None
    if isinstance(t, Suffices):
        return t.prop     # the steps after "it suffices to show P" prove P
    if isinstance(t, (Chain, Choose, Have, Let, Obtain, Auto)):
        return goal
    if isinstance(t, Fix):
        return _after_intro(goal, t.vars, len(t.hyps))
    if isinstance(t, Take):
        return _after_take(goal, t.witnesses) if t.such_that is None else None
    if isinstance(t, SupposeNot):
        from .expr import FALSE

        return FALSE      # by contradiction: the goal is False
    if isinstance(t, CaseSplit):
        for c in t.cases:
            _track_goals(c.body, goal, out)
        return None
    if isinstance(t, InductionOn):
        _track_induction(t, goal, out)
        return None
    return None


def _after_intro(goal: Any, variables: Iterable[Any], n_hyps: int) -> Any:
    """The goal after ``intro x y (h : P)``: ∀-variables renamed to the fixed ones, then
    implications' premises consumed (None if the goal does not have that shape)."""
    from .expr import Logic, Quant
    from .ops import substitute

    for v in variables:
        if not (isinstance(goal, Quant) and goal.kind == "forall" and goal.vars):
            return None
        bound, rest = goal.vars[0], goal.vars[1:]
        body = substitute(goal.body, (bound, v)) if bound is not v else goal.body
        goal = Quant("forall", tuple(rest), body) if rest else body
    for _ in range(n_hyps):
        if not (isinstance(goal, Logic) and goal.op == "implies"):
            return None
        goal = goal.rhs
    return goal


def _after_take(goal: Any, witnesses: Iterable[Any]) -> Any:
    from .expr import Quant
    from .ops import substitute

    ws = list(witnesses)
    if not (isinstance(goal, Quant) and goal.kind == "exists" and len(goal.vars) >= len(ws)):
        return None
    body = substitute(goal.body, *zip(goal.vars[:len(ws)], ws, strict=True))
    rest = goal.vars[len(ws):]
    return Quant("exists", tuple(rest), body) if rest else body


def _track_induction(t: Any, goal: Any, out: dict[Any, Any]) -> None:
    """Base case: the goal at 0; step: the goal at k + 1, the hypothesis the goal at k."""
    from .expr import Lit
    from .ops import free_vars, substitute

    if goal is None or not any(v is t.var for v in free_vars(goal)):
        _track_goals(t.base, None, out)
        _track_goals(t.step, None, out)
        return
    zero = Lit(Fraction(0), t.var.sort)
    _track_goals(t.base, substitute(goal, (t.var, zero)), out)
    out[("ih", id(t))] = substitute(goal, (t.var, t.k))
    _track_goals(t.step, substitute(goal, (t.var, t.k + 1)), out)


def _split_names(names: Iterable[str], prop: Any) -> tuple[tuple[str, Any], ...]:
    """``obtain ⟨x, h₁, h₂⟩ : ∃ x, A ∧ B``: h₁ states A, h₂ states B (the last name takes
    the rest of the conjunction)."""
    from .expr import Logic

    names = [n for n in names if n]
    out = []
    for i, n in enumerate(names):
        if i < len(names) - 1 and isinstance(prop, Logic) and prop.op == "and":
            out.append((n, prop.lhs))
            prop = prop.rhs
        else:
            out.append((n, prop))
            break
    return tuple(out)


def derivation(thm: Any) -> Derivation:
    """The derivation graph of a theorem's (prepared) proof."""
    hyps = [h.name for h in thm.assumptions]
    every = set(hyps) | _all_names(thm.proof) | {"this"}
    nodes = [Node(h.name, "hypothesis", h.prop, (), (), (), (h.name,), None)
             for h in thm.assumptions]
    out: list[Node] = []
    _walk(thm.proof, tuple(hyps), every, out)
    goals: dict[int, Any] = {}
    _track_goals(thm.proof, getattr(thm, "conclusion", None), goals)
    return Derivation(thm.name, (*nodes, *out), goals)


__all__ = ["Derivation", "Node", "derivation"]

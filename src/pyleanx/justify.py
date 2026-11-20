"""The justification engine: how a written step is proved from what it cites.

A step of a written proof (``pl.claim(P, because=…)``) becomes ``have h : P := by first |
…``: Lean tries the alternatives in order and the kernel checks whichever succeeds. This
module assembles those alternatives from *rules*, the way each PyTorch operation brings
its own derivative: the core registers the domain-free rules (use a hypothesis or a cited
fact, symmetry of = and ≠, parts of a conjunction, a lemma applied to cited facts,
rewriting, arithmetic decision procedures), and a domain pack registers the rules of its
vocabulary (the geometry pack: ∠ABC = ∠CBA, the vertices of a triangle are distinct, …).

Rules live in ordered *slots*:

* ``"step"``: the alternatives tried for the step itself;
* ``"close"``: closers for the side goals left after applying a cited lemma;
* ``"cheap_close"``: the closers used after a cheap (reducible-only) application.

Within a slot, rules run by ``priority`` (then registration order). A pack's rules are
active only in theorems that use the pack's vocabulary (see :func:`register_pack`), so a
proof about integers is not searched with geometry's rules. Lean's heartbeat budget is
shared by every alternative of every step of a theorem, so cheap rules come first and
the number of alternatives per step is bounded.

Nothing here can make a step count as proved: Lean checks every alternative it uses.
"""

from __future__ import annotations

import contextvars
from collections.abc import Callable, Iterable, Iterator
from contextlib import contextmanager
from dataclasses import dataclass, replace
from typing import Any

SLOTS = ("step", "close", "cheap_close")


@dataclass(frozen=True)
class Step:
    """What a rule sees of a step: the cited facts as Lean text, and the closers in force."""

    facts: tuple[str, ...]      # every cited fact, rendered
    lemmas: tuple[str, ...]     # cited facts that are names or applied lemmas (not statements)
    avoid: tuple[str, ...] = ()  # facts the step must not use (Theorem(avoid=…))
    close: str = ""             # "first | …" of the "close" slot (filled by the engine)
    cheap: str = ""             # "first | …" of the "cheap_close" slot

    @property
    def names(self) -> tuple[str, ...]:
        """Cited facts that are single names (can be applied, reversed, projected)."""
        return tuple(f for f in self.facts if " " not in f)

    @property
    def h(self) -> str:
        """`` [f₁, f₂]`` for ``linarith``-like tactics (empty if nothing is cited)."""
        return (" [" + ", ".join(self.facts) + "]") if self.facts else ""

    @property
    def hs(self) -> str:
        """`` [f₁, -avoided]`` for ``simp``-like tactics."""
        args = list(self.facts) + [f"-{a}" for a in self.avoid]
        return (" [" + ", ".join(args) + "]") if args else ""


Make = Callable[[Step], Iterable[str]]


@dataclass(frozen=True)
class Rule:
    slot: str
    priority: float
    make: Make
    pack: str = "core"
    name: str = ""


@dataclass(frozen=True)
class Pack:
    """A domain pack's identity for the engine: the vocabulary that activates its rules."""

    name: str
    sorts: frozenset[str] = frozenset()      # sort names, e.g. {"Point"}
    symbols: tuple[str, ...] = ()            # Lean name prefixes, e.g. ("MeasureTheory.",)
    imports: tuple[str, ...] = ()            # Lean modules its rules need


_RULES: list[Rule] = []
_PACKS: dict[str, Pack] = {}
#: packs active while one theorem is rendered; None = all registered packs
_ACTIVE: contextvars.ContextVar[frozenset[str] | None] = contextvars.ContextVar(
    "pyleanx_active_packs", default=None)


def register_pack(name: str, *, sorts: Iterable[str] = (), symbols: Iterable[str] = (),
                  imports: Iterable[str] = ()) -> Pack:
    """Declare a domain pack: its rules apply to theorems using one of ``sorts`` or a symbol
    whose Lean name starts with one of ``symbols``, and the Lean modules in ``imports`` (what
    its rules need) are imported for those theorems. Registering again replaces it."""
    pack = Pack(name, frozenset(sorts), tuple(symbols), tuple(imports))
    _PACKS[name] = pack
    return pack


def add_rule(slot: str, priority: float, make: Make | str | Iterable[str], *,
             pack: str = "core", name: str = "") -> Rule:
    """Register a rule. ``make`` is a function of the :class:`Step`, or fixed tactic text.

    Registering a rule with the same ``(pack, name)`` again replaces it, so a module can be
    reloaded without doubling its rules.
    """
    if slot not in SLOTS:
        raise ValueError(f"unknown slot {slot!r}; slots are {SLOTS}")
    if pack != "core" and pack not in _PACKS:
        raise ValueError(f"register the pack {pack!r} (register_pack) before its rules")
    if isinstance(make, str):
        text = make
        fn: Make = lambda _s: (text,)  # noqa: E731
    elif callable(make):
        fn = make
    else:
        texts = tuple(make)
        fn = lambda _s: texts  # noqa: E731
    r = Rule(slot, priority, fn, pack, name)
    if name:
        _RULES[:] = [x for x in _RULES if (x.pack, x.name) != (pack, name)]
    _RULES.append(r)
    return r


def rules(slot: str, active: frozenset[str] | None = None) -> list[Rule]:
    """The rules of ``slot`` in force, in order (``active=None``: every pack)."""
    found = [r for r in _RULES if r.slot == slot
             and (r.pack == "core" or active is None or r.pack in active)]
    order = {id(r): i for i, r in enumerate(_RULES)}
    return sorted(found, key=lambda r: (r.priority, order[id(r)]))


def packs() -> dict[str, Pack]:
    return dict(_PACKS)


def packs_using(sorts: Iterable[str], symbols: Iterable[str]) -> frozenset[str]:
    """The packs whose vocabulary occurs among ``sorts`` and Lean ``symbols``."""
    sorts, symbols = set(sorts), set(symbols)
    return frozenset(p.name for p in _PACKS.values()
                     if p.sorts & sorts
                     or any(s.startswith(pre) for s in symbols for pre in p.symbols))


@contextmanager
def active_packs(names: frozenset[str] | None) -> Iterator[None]:
    """Within the block, only the core rules and those of ``names`` apply."""
    token = _ACTIVE.set(names)
    try:
        yield
    finally:
        _ACTIVE.reset(token)


def current_packs() -> frozenset[str] | None:
    return _ACTIVE.get()


def _texts(slot: str, step: Step, active: frozenset[str] | None) -> list[str]:
    return [t for r in rules(slot, active) for t in r.make(step)]


# --- compact Lean: the side-goal closers written once per file, as a macro ------------
# Spelled out, the closers of side goals are repeated inside every "apply a cited lemma"
# alternative of every step, and Lean spends most of a check parsing them (the 7 Euclid
# proofs: 888 KB of Lean, parsing 19 s of 38 s). While a module is rendered, the
# step-independent closers become one macro per file (`pyleanx_close_…`) that the steps
# call; Lean's work for those proofs halves (19 s). Writing every step's search as a macro
# too was measured and is worse: each macro is compiled like a program. Hygiene is off in
# the macros, so the hypotheses they use are the ones in scope where they are called.

#: macro name -> its Lean definition, while a module is rendered (None: write in full)
_MACROS: contextvars.ContextVar[dict[str, list[str]] | None] = contextvars.ContextVar(
    "pyleanx_macros", default=None)


@contextmanager
def collecting_macros() -> Iterator[dict[str, list[str]]]:
    """Within the block, steps call macros; the definitions are collected in the dict."""
    found: dict[str, list[str]] = {}
    token = _MACROS.set(found)
    try:
        yield found
    finally:
        _MACROS.reset(token)


def _macro(kind: str, alts: list[str]) -> str:
    """The name of a macro running ``first | alts…`` (registered for the module)."""
    import hashlib

    found = _MACROS.get()
    assert found is not None
    name = f"pyleanx_{kind}_" + hashlib.sha256("\n".join(alts).encode()).hexdigest()[:12]
    if name not in found:
        found[name] = ["set_option hygiene false in",
                       f'macro "{name}" : tactic => `(tactic|',
                       "  first",
                       *(f"    | {a}" for a in alts[:-1]),
                       f"    | {alts[-1]})"]
    return name


def _first(slot: str, step: Step, active: frozenset[str] | None) -> str:
    """``first | …`` of a closer slot; its step-independent prefix as a macro if compact."""
    items = _texts(slot, step, active)
    if _MACROS.get() is not None:
        common = _texts(slot, Step((), (), step.avoid), active)
        if common and items[:len(common)] == common:
            items = [_macro("close", common), *items[len(common):]]
    return "first | " + " | ".join(items)


# --- certificates: search in Python, checking in Lean ---------------------------------
# A rule writes tactics from the *text* of what a step cites, and Lean searches. A
# certifier sees the *mathematics*: the statement of the step and the statements of the
# cited hypotheses and steps, as PyLeanX expressions. It may search as long as it likes in
# Python (linear algebra, a solver, numerics) and returns a certificate: tactic text that
# Lean only has to check, e.g. ``linear_combination 2 * h1 - h2`` instead of a search by
# ``linarith``/``nlinarith`` inside Lean's time budget. Certificates are tried before the
# rules; a wrong one fails like any other alternative and the rules still run. Nothing a
# certifier returns is trusted: the kernel checks the proof term built from it.


@dataclass(frozen=True)
class Goal:
    """What a certifier sees of a step."""

    statement: Any                         # the Expr the step states
    given: tuple[tuple[str, Any], ...]     # cited hypotheses/steps: (Lean name, statement)
    facts: tuple[str, ...]                 # every cited fact, as Lean text


Certify = Callable[[Goal], "str | Iterable[str] | None"]


@dataclass(frozen=True)
class Certifier:
    name: str
    certify: Certify
    priority: float = 0
    pack: str = "core"
    imports: tuple[str, ...] = ()   # Lean modules its certificates need


_CERTIFIERS: list[Certifier] = []
#: id(step) -> {Lean name: statement} of what is in scope at that step, while a theorem is
#: rendered (from its derivation graph)
_STATEMENTS: contextvars.ContextVar[dict[int, dict[str, Any]] | None] = \
    contextvars.ContextVar("pyleanx_statements", default=None)


def register_certifier(name: str, certify: Certify, *, priority: float = 0,
                       pack: str = "core", imports: Iterable[str] = ()) -> Certifier:
    """Register a certifier (registering the same ``(pack, name)`` again replaces it).

    ``certify(goal)`` returns tactic text, several alternatives, or ``None`` (no
    certificate). It must be deterministic: the generated Lean is fingerprinted.
    """
    if pack != "core" and pack not in _PACKS:
        raise ValueError(f"register the pack {pack!r} (register_pack) before its certifiers")
    c = Certifier(name, certify, priority, pack, tuple(imports))
    _CERTIFIERS[:] = [x for x in _CERTIFIERS if (x.pack, x.name) != (pack, name)]
    _CERTIFIERS.append(c)
    return c


def unregister_certifier(name: str, *, pack: str = "core") -> None:
    _CERTIFIERS[:] = [x for x in _CERTIFIERS if (x.pack, x.name) != (pack, name)]


def certifiers(active: frozenset[str] | None = None) -> list[Certifier]:
    """The certifiers in force, in order (``active=None``: every pack)."""
    found = [c for c in _CERTIFIERS
             if c.pack == "core" or active is None or c.pack in active]
    order = {id(c): i for i, c in enumerate(_CERTIFIERS)}
    return sorted(found, key=lambda c: (c.priority, order[id(c)]))


def certifier_imports() -> tuple[str, ...]:
    return tuple(dict.fromkeys(i for c in _CERTIFIERS for i in c.imports))


@contextmanager
def known_statements(statements: dict[int, dict[str, Any]] | None) -> Iterator[None]:
    """Within the block, certifiers see, for each step (by ``id``), the statements of the
    names in its scope (see :meth:`pyleanx.derivation.Derivation.given`)."""
    token = _STATEMENTS.set(statements)
    try:
        yield
    finally:
        _STATEMENTS.reset(token)


def statements_for(step: object) -> dict[str, Any]:
    """The statements in scope at ``step`` while its theorem is rendered (else empty)."""
    return (_STATEMENTS.get() or {}).get(id(step), {})


def certificates(statement: Any, facts: Iterable[str],
                 statements: dict[str, Any] | None = None) -> list[tuple[str, str]]:
    """``(certifier, tactic)`` for a step stating ``statement`` from ``facts``.

    A certifier that raises is skipped with a warning: a certifier can only add
    alternatives, never stop a proof from being checked.
    """
    import warnings

    known = statements or {}
    facts = tuple(facts)
    goal = Goal(statement, tuple((f, known[f]) for f in facts if f in known), facts)
    out: list[tuple[str, str]] = []
    for c in certifiers(current_packs()):
        try:
            found = c.certify(goal)
        except Exception as exc:  # noqa: BLE001 - see the docstring
            warnings.warn(f"certifier {c.pack}:{c.name} failed: {type(exc).__name__}: {exc}",
                          RuntimeWarning, stacklevel=2)
            continue
        if found is None:
            continue
        for text in ((found,) if isinstance(found, str) else found):
            out.append((c.name, text))
    return out


def alternatives(facts: Iterable[str], lemmas: Iterable[str],
                 avoid: Iterable[str] = (), *, goal: Any = None,
                 given: dict[str, Any] | None = None) -> list[str]:
    """The tactic alternatives for one step, in order, without repetitions.

    With ``goal`` (the statement of the step) and ``given`` (the statements in its scope,
    by Lean name), the certificates come first.
    """
    active = current_packs()
    facts = tuple(facts)
    step = Step(facts, tuple(lemmas), tuple(avoid))
    step = replace(step, cheap=_first("cheap_close", step, active))
    step = replace(step, close=_first("close", step, active))
    certs = [t for _, t in certificates(goal, facts, given)] if goal is not None else []
    # an alternative tried twice cannot succeed the second time
    alts = list(dict.fromkeys([*certs, *_texts("step", step, active)]))
    return alts


# =====================================================================================
# The core rules (domain-free)
# =====================================================================================

# --- closers of side goals ------------------------------------------------------------
for _p, _t in ((10, "assumption"), (20, "exact Ne.symm ‹_›"), (40, "exact Eq.symm ‹_›"),
               (50, "exact ne_of_gt ‹_›"), (70, "rfl"), (80, "omega"), (90, "fun_prop"),
               (100, "positivity"), (110, "linarith"), (150, "(simp_all; done)")):
    add_rule("close", _p, _t, name=f"close:{_t}")
for _p, _t in ((10, "assumption"), (20, "exact Ne.symm ‹_›"), (70, "rfl"), (110, "linarith")):
    add_rule("cheap_close", _p, _t, name=f"cheap:{_t}")


def _side_by_cited(s: Step) -> Iterable[str]:
    # a side condition left by applying one cited fact may be another cited fact ("by A,
    # since B"), possibly for every element of a set ("∀ i ∈ s, …")
    for f in s.lemmas:
        if " " not in f:
            yield from (f"exact {f}", f"(intros; exact {f})", f"(apply {f} <;> assumption)",
                        f"(intros; apply {f})")


add_rule("close", 1000, _side_by_cited, name="close:cited")


# --- the step itself ------------------------------------------------------------------
def _r(priority: float, name: str) -> Callable[[Make], Make]:
    def deco(fn: Make) -> Make:
        add_rule("step", priority, fn, name=name)
        return fn
    return deco


add_rule("step", 10, ("assumption", "contradiction"), name="hypothesis")


@_r(20, "cited, reducible")
def _cited_reducible(s: Step) -> Iterable[str]:
    # Cheap first: matching with reducible unfolding only fails at once on a mismatch.
    # (Unrestricted matching of, say, an angle against π/3 unfolds definitions until
    # Lean's time budget for the whole theorem is gone; then nothing later can run.)
    return [f"(with_reducible exact {f})" for f in s.facts]


@_r(30, "cited reversed, reducible")
def _cited_reversed_reducible(s: Step) -> Iterable[str]:
    return [f"(with_reducible exact ({f}).symm)" for f in s.names]


@_r(40, "apply cited, cheap side goals")
def _apply_cheap(s: Step) -> Iterable[str]:
    return [f"((with_reducible apply {f}); all_goals ({s.cheap}))" for f in s.lemmas]


@_r(50, "linear arithmetic")
def _linarith(s: Step) -> Iterable[str]:
    return [f"linarith{s.h}"]


@_r(60, "cited")
def _cited(s: Step) -> Iterable[str]:
    return [f"exact {f}" for f in s.facts]


@_r(70, "cited reversed")
def _cited_reversed(s: Step) -> Iterable[str]:
    return [f"exact ({f}).symm" for f in s.names]


@_r(80, "conjunction of cited")
def _conjunction(s: Step) -> Iterable[str]:
    if len(s.facts) < 2:
        return []
    return ["exact ⟨" + ", ".join(f if " " not in f else f"({f})" for f in s.facts) + "⟩"]


@_r(90, "part of cited")
def _projection(s: Step) -> Iterable[str]:
    return [f"exact {f}{proj}" for f in s.names
            for proj in (".1", ".2", ".2.1", ".2.2", ".1.1", ".1.2")]


@_r(100, "apply cited")
def _apply(s: Step) -> Iterable[str]:
    return [f"(apply {f}; all_goals ({s.close}))" for f in s.lemmas]


def _pairs(s: Step) -> bool:
    # Lean's time budget is per declaration, so the pairs are capped: a step citing dozens
    # of facts would otherwise try thousands of applications and time out.
    return len(s.lemmas) * len(s.names) <= 150


@_r(110, "lemma of cited, reducible")
def _lemma_of_cited_reducible(s: Step) -> Iterable[str]:
    # "by L, since h"; reducible matching first, in both orientations, so a fact stated the
    # other way round fails at once instead of unfolding definitions
    if not _pairs(s):
        return []
    return ([f"(with_reducible exact {f} {g})" for f in s.lemmas for g in s.names if g != f]
            + [f"(with_reducible exact ({f} {g}).symm)" for f in s.lemmas for g in s.names
               if g != f])


@_r(130, "lemma of two cited")
def _lemma_of_two(s: Step) -> Iterable[str]:
    # "by L, from h₁ and h₂", in either order
    if len(s.lemmas) * len(s.names) ** 2 > 120:  # a cited family ("CPCTC") would explode
        return []
    return [f"exact {f} {g} {k}" for f in s.lemmas for g in s.names for k in s.names
            if len({f, g, k}) == 3]


@_r(140, "lemma of cited")
def _lemma_of_cited(s: Step) -> Iterable[str]:
    if not _pairs(s):
        return []
    return [f"exact {f} {g}" for f in s.lemmas for g in s.names if g != f]


@_r(150, "rewrite with cited")
def _rewrite(s: Step) -> Iterable[str]:
    return ([f"(rw [{f}]; done)" for f in s.lemmas]
            + [f"(rw [{f}]; simp{s.hs}; done)" for f in s.lemmas])


@_r(170, "normalise with cited")
def _normalise(s: Step) -> Iterable[str]:
    # normalising everything with a cited rule, then closing
    return [f"(simp only [{f}] at *; first | assumption | linarith | (simp_all; done))"
            for f in s.lemmas]


@_r(180, "substitute cited")
def _substitute(s: Step) -> Iterable[str]:
    # substituting a cited equation (f(x) = 3x + 1), then algebra, also inside |…|
    return [f"(simp only [{f}]; first | ring1 | (congr 1; ring1))" for f in s.lemmas]


@_r(190, "half of cited")
def _half(s: Step) -> Iterable[str]:
    # one half of a conjunction / one direction of an equivalence; matching limited to
    # reducible definitions and instances, so the wrong half fails at once
    return [f"(with_reducible_and_instances apply {half}; "
            f"with_reducible_and_instances apply {f}; all_goals ({s.close}))"
            for f in s.lemmas for half in ("And.left", "And.right", "Iff.mp", "Iff.mpr")]


@_r(200, "cited up to set order")
def _set_order(s: Step) -> Iterable[str]:
    # a cited fact about the same elements listed in another order ({A, B, C} = {B, A, C})
    return [f"(convert {f} using {d}; ext; simp only [Set.mem_insert_iff, "
            f"Set.mem_singleton_iff]; tauto)" for f in s.names for d in (2, 1)]


@_r(210, "decision procedures")
def _decide(s: Step) -> Iterable[str]:
    return ["rfl", "ring1", "omega", "positivity", "fun_prop", f"linarith{s.h}"]


@_r(220, "normalise and decide")
def _normalise_decide(s: Step) -> Iterable[str]:
    return ["(congr 1; ring1)", "(push_cast; ring1)",
            f"(norm_num{s.hs}; done)", f"(simp{s.hs}; done)", f"(simp{s.hs}; ring1)",
            f"nlinarith{s.h}", "(field_simp; done)", "(field_simp; ring1)",
            f"(simp_all{s.hs}; done)", f"(constructor; all_goals ({s.close}))"]


@_r(1000, "general search")
def _general(s: Step) -> Iterable[str]:
    if s.avoid:  # aesop's and grind's simp sets cannot be restricted here
        return []
    return ["(aesop; done)", "grind"]


__all__ = ["SLOTS", "Certifier", "Goal", "Pack", "Rule", "Step", "active_packs", "add_rule",
           "alternatives", "certificates", "certifier_imports", "certifiers",
           "current_packs", "known_statements", "packs", "packs_using", "register_certifier",
           "register_pack", "rules", "statements_for", "unregister_certifier"]

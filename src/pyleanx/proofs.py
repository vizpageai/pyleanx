"""Proof and tactic IR.

Every emitted tactic is constructed from a recognised tactic node; names and
lemma references are validated identifiers. The single escape hatch,
:func:`raw_tactic`, produces an *untrusted* node that the verification policy
rejects unless explicitly enabled (intended for AI-generated proof text).
"""

from __future__ import annotations

import re
import textwrap
from collections.abc import Iterable
from dataclasses import dataclass, field
from typing import Any, ClassVar

from ._origin import Origin, caller_origin
from .errors import TacticError
from .expr import Expr, Var
from .names import validate_identifier, validate_qualified_name

# =====================================================================================
# Proof terms (arguments of exact / apply / rw / simp)
# =====================================================================================


@dataclass(frozen=True)
class Name:
    """A hypothesis or library declaration referenced by (qualified) name."""

    name: str
    imports: tuple[str, ...] = ()
    #: What the fact says, in words (shown when a written proof is printed).
    label: str = field(default="", compare=False)

    def __post_init__(self) -> None:
        validate_qualified_name(self.name, "lemma/hypothesis name")
        for imp in self.imports:
            validate_qualified_name(imp, "import module")

    def __call__(self, *args: TermLike) -> TermApp:
        return TermApp(self, tuple(_term(a) for a in args))

    def canonical(self) -> Any:
        return ["name", self.name]


@dataclass(frozen=True)
class LibraryFact(Name):
    """A textbook fact PyLeanX ships as a Lean theorem *with its proof*, for results that
    Mathlib does not state in the form a proof cites (e.g. corresponding angles).

    The declaration is emitted into every Lean file that cites it, so Lean checks its
    proof each time and its axioms are part of the citing theorem's audit.
    """

    lean: str = field(default="", compare=False)
    requires: tuple[LibraryFact, ...] = field(default=(), compare=False)


#: Shipped facts by Lean name (so serialized proofs that cite them can be rebuilt).
LIBRARY_FACTS: dict[str, LibraryFact] = {}


def library_fact(name: str, lean: str, *imports: str, label: str = "",
                 requires: Iterable[LibraryFact] = ()) -> LibraryFact:
    fact = LibraryFact(name, tuple(imports), label=label, lean=textwrap.dedent(lean).strip(),
                       requires=tuple(requires))
    LIBRARY_FACTS[name] = fact
    return fact


@dataclass(frozen=True)
class TermApp:
    """Application of a named lemma to arguments, e.g. ``mul_pos hx hy``."""

    fn: Name
    args: tuple[Term, ...]

    def canonical(self) -> Any:
        return ["app", self.fn.canonical(), [_canon_term(a) for a in self.args]]


Term = Name | TermApp | Expr
TermLike = Term | str


def _term(value: object) -> Term:
    if isinstance(value, (Name, TermApp, Expr)):
        return value
    if isinstance(value, str):
        return Name(value)
    if hasattr(value, "name") and type(value).__name__ == "Theorem":
        return Name(value.name)  # reuse a previously declared theorem as a lemma
    hook = getattr(type(value), "__pyleanx_term__", None)  # e.g. pl.mathlib declarations
    if hook is not None:
        return hook(value)
    raise TacticError(f"expected a hypothesis name, pl.ref(...), or expression; got {value!r}")


def _canon_term(t: Term) -> Any:
    return t.canonical()


def ref(name: object, imports: Iterable[str] = ()) -> Name:
    """Reference a Mathlib/core declaration (``pl.ref("sq_nonneg")``) or a Theorem."""
    if type(name).__name__ == "Theorem":
        return Name(name.name)  # type: ignore[attr-defined]
    return Name(name, tuple(imports))  # type: ignore[arg-type]


def hyp(name: str) -> Name:
    """Reference a local hypothesis by name."""
    validate_identifier(name, "hypothesis name")
    return Name(name)


def term_imports(t: Term) -> tuple[str, ...]:
    if isinstance(t, LibraryFact):
        return (*t.imports, *(i for r in t.requires for i in term_imports(r)))
    if isinstance(t, Name):
        return t.imports
    if isinstance(t, TermApp):
        out = list(t.fn.imports)
        for a in t.args:
            out.extend(term_imports(a))
        return tuple(out)
    if isinstance(t, Expr):
        from .imports import expr_imports

        return tuple(expr_imports(t))
    return ()


# =====================================================================================
# Tactics
# =====================================================================================


@dataclass(frozen=True)
class Tactic:
    origin: Origin | None = field(default=None, compare=False, kw_only=True)

    #: Lean modules this tactic needs (beyond the core prelude).
    IMPORTS: ClassVar[tuple[str, ...]] = ()

    def imports(self) -> tuple[str, ...]:
        return self.IMPORTS

    def canonical(self) -> Any:  # pragma: no cover - abstract
        raise NotImplementedError

    def flat(self) -> tuple[Tactic, ...]:
        return (self,)

    def sub_tactics(self) -> tuple[Tactic, ...]:
        """Tactics nested inside this one (for policy checks and imports)."""
        return ()

    def __str__(self) -> str:
        """The Lean tactic text this node renders to."""
        from .render.lean import render_tactic_lines

        return "\n".join(render_tactic_lines(self))

    def __rshift__(self, other: Tactic) -> Steps:
        """``pl.intro("h") >> pl.exact("h")`` sequences tactics."""
        return steps(self, other)


@dataclass(frozen=True)
class _Simple(Tactic):
    keyword: str = ""

    def canonical(self) -> Any:
        return [self.keyword]


@dataclass(frozen=True)
class Ring(_Simple):
    keyword: str = "ring"
    IMPORTS = ("Mathlib.Tactic.Ring",)


@dataclass(frozen=True)
class Omega(_Simple):
    keyword: str = "omega"


@dataclass(frozen=True)
class Positivity(_Simple):
    keyword: str = "positivity"
    IMPORTS = ("Mathlib.Tactic.Positivity",)


@dataclass(frozen=True)
class Rfl(_Simple):
    keyword: str = "rfl"


@dataclass(frozen=True)
class Decide(_Simple):
    keyword: str = "decide"


@dataclass(frozen=True)
class Constructor(_Simple):
    keyword: str = "constructor"


@dataclass(frozen=True)
class Assumption(_Simple):
    keyword: str = "assumption"


@dataclass(frozen=True)
class Aesop(_Simple):
    """``aesop``: Mathlib's best-first proof search (logic, sets, simple goals)."""

    keyword: str = "aesop"
    IMPORTS = ("Aesop",)


@dataclass(frozen=True)
class LibrarySearch(_Simple):
    """``exact?``: search the imported library for a lemma that closes the goal."""

    keyword: str = "exact?"


@dataclass(frozen=True)
class _WithLemmas(Tactic):
    keyword: str = ""
    lemmas: tuple[Term, ...] = ()

    def imports(self) -> tuple[str, ...]:
        out = list(self.IMPORTS)
        for t in self.lemmas:
            out.extend(term_imports(t))
        return tuple(out)

    def canonical(self) -> Any:
        return [self.keyword, [_canon_term(t) for t in self.lemmas]]


@dataclass(frozen=True)
class Linarith(_WithLemmas):
    keyword: str = "linarith"
    IMPORTS = ("Mathlib.Tactic.Linarith",)


@dataclass(frozen=True)
class Nlinarith(_WithLemmas):
    keyword: str = "nlinarith"
    IMPORTS = ("Mathlib.Tactic.Linarith",)


@dataclass(frozen=True)
class NormNum(_WithLemmas):
    keyword: str = "norm_num"
    IMPORTS = ("Mathlib.Tactic.NormNum",)


@dataclass(frozen=True)
class Simp(_WithLemmas):
    keyword: str = "simp"
    only: bool = False
    at: tuple[str, ...] = ()

    def canonical(self) -> Any:
        return ["simp", self.only, [_canon_term(t) for t in self.lemmas], list(self.at)]


@dataclass(frozen=True)
class Intro(Tactic):
    names: tuple[str, ...] = ()

    def canonical(self) -> Any:
        return ["intro", list(self.names)]


@dataclass(frozen=True)
class Exact(Tactic):
    term: Term = None  # type: ignore[assignment]

    def imports(self) -> tuple[str, ...]:
        return term_imports(self.term)

    def canonical(self) -> Any:
        return ["exact", _canon_term(self.term)]


@dataclass(frozen=True)
class Apply(Tactic):
    term: Term = None  # type: ignore[assignment]

    def imports(self) -> tuple[str, ...]:
        return term_imports(self.term)

    def canonical(self) -> Any:
        return ["apply", _canon_term(self.term)]


@dataclass(frozen=True)
class Rewrite(Tactic):
    rules: tuple[tuple[Term, bool], ...] = ()  # (rule, reverse?)
    at: tuple[str, ...] = ()

    def imports(self) -> tuple[str, ...]:
        out: list[str] = []
        for t, _ in self.rules:
            out.extend(term_imports(t))
        return tuple(out)

    def canonical(self) -> Any:
        return ["rw", [[_canon_term(t), rev] for t, rev in self.rules], list(self.at)]


@dataclass(frozen=True)
class Use(Tactic):
    witnesses: tuple[Expr, ...] = ()
    IMPORTS = ("Mathlib.Tactic.Use",)

    def canonical(self) -> Any:
        return ["use", [w.canonical() for w in self.witnesses]]


@dataclass(frozen=True)
class Steps(Tactic):
    tactics: tuple[Tactic, ...] = ()

    def imports(self) -> tuple[str, ...]:
        return tuple(i for t in self.tactics for i in t.imports())

    def sub_tactics(self) -> tuple[Tactic, ...]:
        return self.tactics

    def flat(self) -> tuple[Tactic, ...]:
        return tuple(x for t in self.tactics for x in t.flat())

    def canonical(self) -> Any:
        return ["steps", [t.canonical() for t in self.flat()]]


@dataclass(frozen=True)
class Branches(Tactic):
    """One proof per open goal, rendered as ``·`` bullets."""

    branches: tuple[Tactic, ...] = ()

    def imports(self) -> tuple[str, ...]:
        return tuple(i for t in self.branches for i in t.imports())

    def sub_tactics(self) -> tuple[Tactic, ...]:
        return self.branches

    def canonical(self) -> Any:
        return ["branches", [t.canonical() for t in self.branches]]


@dataclass(frozen=True)
class RawTactic(Tactic):
    """UNTRUSTED opaque tactic text (e.g. produced by an LLM). Policy-gated."""

    text: str = ""
    extra_imports: tuple[str, ...] = ()

    def imports(self) -> tuple[str, ...]:
        return self.extra_imports

    def canonical(self) -> Any:
        return ["raw", self.text]


# =====================================================================================
# Raw tactic screening
# =====================================================================================

_FORBIDDEN_WORDS = (
    "set_option axiom theorem lemma def abbrev instance opaque unsafe extern implemented_by "
    "macro macro_rules syntax elab elab_rules run_tac run_cmd run_elab run_meta import "
    "namespace section attribute notation infix infixl infixr prefix postfix initialize "
    "builtin_initialize declare_syntax_cat example structure class inductive mutual "
    "universe variable open export"
).split()
_FORBIDDEN_RE = re.compile(
    r"(?<![\w.'])(" + "|".join(map(re.escape, _FORBIDDEN_WORDS)) + r")(?![\w'])"
)
_HASH_CMD_RE = re.compile(r"#[A-Za-z_]")
_DEBUG_RE = re.compile(r"\bdebug\.|\bLean\.(Elab|Meta|Compiler)\b|\btrustCompiler\b")


def screen_raw_tactic(text: str) -> list[str]:
    """Return reasons why ``text`` is unsafe to splice into a ``by`` block (empty = ok).

    This is a defence-in-depth heuristic, not a security boundary: the kernel check
    and position-attributed axiom audit remain authoritative.
    """
    problems: list[str] = []
    if any(ord(c) < 32 and c not in "\n\t" for c in text):
        problems.append("control characters")
    if "/-" in text or "-/" in text:
        problems.append("block comments")
    for m in _FORBIDDEN_RE.finditer(text):
        problems.append(f"forbidden keyword {m.group(1)!r}")
    if _HASH_CMD_RE.search(text):
        problems.append("#-commands")
    if _DEBUG_RE.search(text):
        problems.append("kernel/compiler/meta-level options or APIs")
    return problems


# =====================================================================================
# Public constructors
# =====================================================================================


def _names(names: Iterable[str]) -> tuple[str, ...]:
    return tuple(validate_identifier(n, "hypothesis name") for n in names)


def _terms(lemmas: Iterable[TermLike]) -> tuple[Term, ...]:
    return tuple(_term(t) for t in lemmas)


def ring() -> Ring:
    """``ring``: proves equalities in commutative (semi)rings, e.g. polynomial identities."""
    return Ring(origin=caller_origin())


def omega() -> Omega:
    """``omega``: decides linear arithmetic over ℕ and ℤ."""
    return Omega(origin=caller_origin())


def positivity() -> Positivity:
    """``positivity``: proves goals ``0 ≤ e``, ``0 < e``, ``e ≠ 0`` from the structure of ``e``."""
    return Positivity(origin=caller_origin())


def rfl() -> Rfl:
    """``rfl``: closes goals that hold by definition (``a = a`` up to computation)."""
    return Rfl(origin=caller_origin())


def decide() -> Decide:
    """``decide``: evaluates a decidable proposition by kernel computation."""
    return Decide(origin=caller_origin())


def constructor() -> Constructor:
    """``constructor``: splits ``p ∧ q`` / ``p ↔ q`` into one goal per component."""
    return Constructor(origin=caller_origin())


def assumption() -> Assumption:
    """``assumption``: closes the goal with a hypothesis that matches it exactly."""
    return Assumption(origin=caller_origin())


def linarith(*lemmas: TermLike) -> Linarith:
    """``linarith [lemmas]``: linear arithmetic over ordered fields, using hypotheses and the given
    facts.
    """
    return Linarith(lemmas=_terms(lemmas), origin=caller_origin())


def nlinarith(*lemmas: TermLike) -> Nlinarith:
    """``nlinarith [lemmas]``: like ``linarith`` but also multiplies hypotheses; pass hints such as
    ``pl.ref("sq_nonneg")(x - y)``.
    """
    return Nlinarith(lemmas=_terms(lemmas), origin=caller_origin())


def norm_num(*lemmas: TermLike) -> NormNum:
    """``norm_num [lemmas]``: normalises numerals and closes numeric goals."""
    return NormNum(lemmas=_terms(lemmas), origin=caller_origin())


def simp(*lemmas: TermLike, only: bool = False, at: str | Iterable[str] = ()) -> Simp:
    """``simp [lemmas]`` (``only=True`` for ``simp only``; ``at="h"`` to simplify a hypothesis)."""
    at_names = _names([at] if isinstance(at, str) else at)
    return Simp(lemmas=_terms(lemmas), only=only, at=at_names, origin=caller_origin())


def intro(*names: str) -> Intro:
    """``intro names``: introduces ``∀``-bound variables or implication premises with the given
    names.
    """
    if not names:
        raise TacticError("intro needs at least one name (anonymous intro is not supported)")
    return Intro(names=_names(names), origin=caller_origin())


def exact(term: TermLike) -> Exact:
    """``exact term``: the term is a complete proof of the goal (a hypothesis, lemma or lemma
    application).
    """
    return Exact(term=_term(term), origin=caller_origin())


def apply(term: TermLike) -> Apply:
    """``apply term``: reduces the goal using a lemma's conclusion; its premises become new goals.
    """
    return Apply(term=_term(term), origin=caller_origin())


def rw(*rules: TermLike | tuple[TermLike, bool], at: str | Iterable[str] = ()) -> Rewrite:
    """``pl.rw("h", pl.rev("add_comm"))``; ``pl.rev(r)`` rewrites right-to-left."""
    if not rules:
        raise TacticError("rw needs at least one rewrite rule")
    out: list[tuple[Term, bool]] = []
    for r in rules:
        if isinstance(r, tuple):
            out.append((_term(r[0]), bool(r[1])))
        else:
            out.append((_term(r), False))
    at_names = _names([at] if isinstance(at, str) else at)
    return Rewrite(rules=tuple(out), at=at_names, origin=caller_origin())


rewrite = rw


def rev(rule: TermLike) -> tuple[Term, bool]:
    """Mark a rewrite rule as right-to-left (``← rule``)."""
    return (_term(rule), True)


def use(*witnesses: object) -> Use:
    """``use witnesses``: supplies witnesses for an ``∃`` goal."""
    from .expr import _lift

    if not witnesses:
        raise TacticError("use needs at least one witness")
    return Use(witnesses=tuple(_lift(w) for w in witnesses), origin=caller_origin())


def steps(*tactics: Tactic) -> Steps:
    """Run tactics in sequence (also written ``t1 >> t2``)."""
    if not tactics:
        raise TacticError("steps() needs at least one tactic")
    for t in tactics:
        if not isinstance(t, Tactic):
            raise TacticError(f"steps() expects tactics, got {t!r}")
    return Steps(tactics=tuple(tactics), origin=caller_origin())


def branches(*proofs: Tactic) -> Branches:
    """One proof per remaining goal, in order (Lean's ``·`` focusing bullets)."""
    if len(proofs) < 1:
        raise TacticError("branches() needs at least one proof")
    for t in proofs:
        if not isinstance(t, Tactic):
            raise TacticError(f"branches() expects tactics, got {t!r}")
    return Branches(branches=tuple(proofs), origin=caller_origin())


def raw_tactic(text: str, imports: Iterable[str] = ()) -> RawTactic:
    """UNTRUSTED tactic text. Rejected by the default policy; see docs/security.md."""
    if not isinstance(text, str) or not text.strip():
        raise TacticError("raw_tactic needs non-empty text")
    imps = tuple(validate_qualified_name(i, "import module") for i in imports)
    cleaned = "\n".join(ln.rstrip() for ln in textwrap.dedent(text).strip("\n").splitlines())
    return RawTactic(text=cleaned, extra_imports=imps, origin=caller_origin())


def contains_raw(t: Tactic) -> bool:
    """Does the tactic tree contain untrusted raw text anywhere (including nested blocks)?"""
    return any(True for _ in iter_raw(t))


def iter_raw(t: Tactic) -> Iterable[RawTactic]:
    if isinstance(t, RawTactic):
        yield t
    for x in t.sub_tactics():
        yield from iter_raw(x)


# =====================================================================================
# Structured proofs (mathematical style) and automation
# =====================================================================================

#: Each alternative must close the goal completely (``done``), so ``auto`` never leaves a
#: partially simplified goal behind.
_AUTO_IMPORTS = ("Mathlib.Tactic.Ring", "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Positivity",
                 "Mathlib.Tactic.NormNum", "Mathlib.Tactic.FieldSimp")


@dataclass(frozen=True)
class Auto(Tactic):
    """Try standard closing tactics in order; succeed only if one closes the goal."""

    hints: tuple[Term, ...] = ()
    aesop: bool = True
    library_search: bool = False

    def imports(self) -> tuple[str, ...]:
        out = list(_AUTO_IMPORTS)
        if self.aesop:
            out.append("Aesop")
        for t in self.hints:
            out.extend(term_imports(t))
        return tuple(out)

    def alternatives(self) -> list[str]:
        from .render.lean import render_term

        h = (" [" + ", ".join(render_term(t) for t in self.hints) + "]") if self.hints else ""
        alts = ["rfl", "ring1", f"(norm_num{h}; done)", f"(simp{h}; done)", f"linarith{h}",
                "positivity", f"nlinarith{h}", "(field_simp; ring1)"]
        if self.aesop:
            alts.append("(aesop; done)")
        if self.library_search:
            alts.append("exact?")
        return alts

    def canonical(self) -> Any:
        return ["auto", [_canon_term(t) for t in self.hints], self.aesop, self.library_search]


def _block(t: Tactic | None) -> list[str]:
    from .render.lean import render_tactic_lines

    return render_tactic_lines(t if t is not None else Auto())


@dataclass(frozen=True)
class Have(Tactic):
    """``have name : P := by …`` (proved by ``auto`` when no proof is given)."""

    name: str = ""
    prop: Expr = None  # type: ignore[assignment]
    proof: Tactic | None = None

    def imports(self) -> tuple[str, ...]:
        return (Auto() if self.proof is None else self.proof).imports()

    def sub_tactics(self) -> tuple[Tactic, ...]:
        return (self.proof,) if self.proof is not None else ()

    def canonical(self) -> Any:
        return ["have", self.name, self.prop.canonical(),
                self.proof.canonical() if self.proof is not None else None]


CALC_RELATIONS = {"=": "=", "<=": "≤", "≤": "≤", "<": "<", ">=": "≥", "≥": "≥", ">": ">",
                  "!=": "≠", "≠": "≠"}


@dataclass(frozen=True)
class Calc(Tactic):
    """``calc a = b := by … ; _ ≤ c := by …`` (a chain of relations)."""

    first: Expr = None  # type: ignore[assignment]
    links: tuple[tuple[str, Expr, Tactic | None], ...] = ()

    def imports(self) -> tuple[str, ...]:
        return tuple(i for _, _, t in self.links for i in (t or Auto()).imports())

    def sub_tactics(self) -> tuple[Tactic, ...]:
        return tuple(t for _, _, t in self.links if t is not None)

    def canonical(self) -> Any:
        return ["calc", self.first.canonical(),
                [[rel, e.canonical(), t.canonical() if t is not None else None]
                 for rel, e, t in self.links]]


@dataclass(frozen=True)
class Show(Tactic):
    """``show P``: state the current goal explicitly (Lean checks it matches)."""

    prop: Expr = None  # type: ignore[assignment]

    def canonical(self) -> Any:
        return ["show", self.prop.canonical()]


@dataclass(frozen=True)
class Obtain(Tactic):
    """``obtain ⟨x, hx⟩ := h``: destructure ∃ / ∧ hypotheses or lemma results."""

    names: tuple[str, ...] = ()
    source: Term = None  # type: ignore[assignment]

    def imports(self) -> tuple[str, ...]:
        return term_imports(self.source)

    def canonical(self) -> Any:
        return ["obtain", list(self.names), _canon_term(self.source)]


@dataclass(frozen=True)
class Cases(Tactic):
    """``rcases h with h₁ | h₂``: split a disjunction (one new goal per alternative)."""

    source: Term = None  # type: ignore[assignment]
    alternatives: tuple[tuple[str, ...], ...] = ()

    def imports(self) -> tuple[str, ...]:
        return term_imports(self.source)

    def canonical(self) -> Any:
        return ["cases", _canon_term(self.source), [list(a) for a in self.alternatives]]


@dataclass(frozen=True)
class Induction(Tactic):
    """``induction n with | zero => … | succ k ih => …`` on a natural number."""

    var: str = ""
    zero: Tactic | None = None
    succ: Tactic | None = None
    succ_names: tuple[str, str] = ("k", "ih")

    def imports(self) -> tuple[str, ...]:
        return tuple(i for t in (self.zero, self.succ) for i in (t or Auto()).imports())

    def sub_tactics(self) -> tuple[Tactic, ...]:
        return tuple(t for t in (self.zero, self.succ) if t is not None)

    def canonical(self) -> Any:
        return ["induction", self.var,
                self.zero.canonical() if self.zero is not None else None,
                self.succ.canonical() if self.succ is not None else None,
                list(self.succ_names)]


@dataclass(frozen=True)
class Unfold(Tactic):
    """``unfold f g``: replace definitions by their bodies."""

    names: tuple[str, ...] = ()

    def canonical(self) -> Any:
        return ["unfold", list(self.names)]


@dataclass(frozen=True)
class Ext(Tactic):
    """``ext i``: prove an equality of functions/vectors pointwise."""

    names: tuple[str, ...] = ()

    def canonical(self) -> Any:
        return ["ext", list(self.names)]


# =====================================================================================
# Written proofs: claims with reasons (pl.claim / pl.conclude / pl.let)
# =====================================================================================

_JUSTIFY_IMPORTS = (*_AUTO_IMPORTS, "Aesop", "Mathlib.Tactic.FunProp",
                    "Mathlib.Tactic.NormNum.Basic", "Mathlib.Tactic.Ring.RingNF")


@dataclass(frozen=True)
class Justify(Tactic):
    """Close one step of a written proof from the cited facts and everything proved so far.

    Standard automation is tried in order (each alternative must close the goal), first
    as stated, then with the proof's local definitions unfolded, then after introducing
    ∀-variables. Lean checks whatever succeeds; nothing is assumed.
    """

    facts: tuple[Term, ...] = ()
    unfold: tuple[str, ...] = ()  # names of local definitions (pl.let) in scope
    avoid: tuple[str, ...] = field(default=(), compare=False)  # set from Theorem(avoid=…)

    def imports(self) -> tuple[str, ...]:
        return (*_JUSTIFY_IMPORTS, *(i for t in self.facts for i in term_imports(t)))

    def _core(self) -> list[str]:
        from .render.lean import render_term

        fs = [render_term(t) for t in self.facts]
        h = (" [" + ", ".join(fs) + "]") if fs else ""
        simp_args = fs + [f"-{a}" for a in self.avoid]
        hs = (" [" + ", ".join(simp_args) + "]") if simp_args else ""
        close = ("first | assumption | rfl | omega | fun_prop | positivity | linarith | "
                 "(simp_all; done)")
        alts = ["assumption", "contradiction"]
        alts += [f"exact {f}" for f in fs]
        lemmas = [f for f, t in zip(fs, self.facts, strict=True) if not isinstance(t, Expr)]
        alts += [f"(apply {f}; all_goals ({close}))" for f in lemmas]
        # a cited lemma applied to another cited fact ("by L, since h")
        alts += [f"exact {f} {g}" for f in lemmas for g in fs if g != f and " " not in g]
        # rewriting with a cited equation, then tidying up
        alts += [f"(rw [{f}]; done)" for f in lemmas]
        alts += [f"(rw [{f}]; simp{hs}; done)" for f in lemmas]
        # One half of a conjunction / one direction of an equivalence. Matching is limited
        # to reducible definitions and instances, so trying the wrong half fails at once
        # instead of unfolding definitions (a timeout there would end the whole search).
        alts += [f"(with_reducible_and_instances apply {half}; "
                 f"with_reducible_and_instances apply {f}; all_goals ({close}))"
                 for f in lemmas for half in ("And.left", "And.right", "Iff.mp", "Iff.mpr")]
        alts += ["rfl", "ring1", "omega", "positivity", "fun_prop", f"linarith{h}",
                 "(congr 1; ring1)", "(push_cast; ring1)",
                 f"(norm_num{hs}; done)", f"(simp{hs}; done)", f"(simp{hs}; ring1)",
                 f"nlinarith{h}", "(field_simp; ring1)", f"(simp_all{hs}; done)",
                 f"(constructor; all_goals ({close}))"]
        if not self.avoid:  # aesop's simp set cannot be restricted here
            alts.append("(aesop; done)")
        return alts

    def alternatives(self) -> list[str]:
        core = self._core()
        one = "first | " + " | ".join(core)
        alts = [*core, f"(intros; {one})"]
        if self.unfold:
            alts.append(f"(intros; simp only [{', '.join(self.unfold)}] at *; {one})")
        return alts

    def canonical(self) -> Any:
        return ["justify", [_canon_term(t) for t in self.facts], list(self.unfold)]


@dataclass(frozen=True)
class Claim(Tactic):
    """A step of a written proof: a statement, the facts it follows from, and a remark.

    Rendered as ``have name : prop := by …``; without an explicit ``proof`` the step is
    closed by :class:`Justify` from ``facts`` and the earlier steps.
    """

    prop: Expr = None  # type: ignore[assignment]
    facts: tuple[Term, ...] = ()
    name: str = ""
    note: str = ""
    proof: Tactic | None = None
    unfold: tuple[str, ...] = ()
    avoid: tuple[str, ...] = field(default=(), compare=False)

    def justification(self) -> Tactic:
        if self.proof is not None:
            return self.proof
        return Justify(self.facts, self.unfold, self.avoid)

    def imports(self) -> tuple[str, ...]:
        return self.justification().imports()

    def sub_tactics(self) -> tuple[Tactic, ...]:
        return (self.proof,) if self.proof is not None else ()

    def canonical(self) -> Any:
        return ["claim", self.name, self.prop.canonical(), [_canon_term(t) for t in self.facts],
                self.note, self.proof.canonical() if self.proof is not None else None,
                list(self.unfold)]


@dataclass(frozen=True)
class Conclude(Tactic):
    """The last step of a written proof: the goal follows from ``facts`` and the claims."""

    facts: tuple[Term, ...] = ()
    note: str = ""
    proof: Tactic | None = None
    unfold: tuple[str, ...] = ()
    avoid: tuple[str, ...] = field(default=(), compare=False)

    def justification(self) -> Tactic:
        if self.proof is not None:
            return self.proof
        return Justify(self.facts, self.unfold, self.avoid)

    def imports(self) -> tuple[str, ...]:
        return self.justification().imports()

    def sub_tactics(self) -> tuple[Tactic, ...]:
        return (self.proof,) if self.proof is not None else ()

    def canonical(self) -> Any:
        return ["conclude", [_canon_term(t) for t in self.facts], self.note,
                self.proof.canonical() if self.proof is not None else None,
                list(self.unfold)]


@dataclass(frozen=True)
class Let(Tactic):
    """``set f : T := value with f_def``: name an expression for the rest of the proof."""

    var: Var = None  # type: ignore[assignment]
    value: Expr = None  # type: ignore[assignment]
    note: str = ""
    IMPORTS = ("Mathlib.Tactic.Set",)

    @property
    def eq_name(self) -> str:
        return f"{self.var.name}_def"

    def imports(self) -> tuple[str, ...]:
        from .imports import expr_imports

        return (*self.IMPORTS, *expr_imports(self.value))

    def canonical(self) -> Any:
        return ["let", self.var.canonical(), self.value.canonical(), self.note]


def with_avoid(t: Tactic, avoid: tuple[str, ...]) -> Tactic:
    """Prepare a proof (see :func:`prepare`) whose gap-filling must not use ``avoid``."""
    return prepare(t, avoid)


def _proof_arg(p: Tactic | None, what: str) -> Tactic | None:
    if p is not None and not isinstance(p, Tactic):
        raise TacticError(f"{what}: proof must be a tactic, got {p!r}")
    return p


def auto(*hints: TermLike, aesop: bool = True, library_search: bool = False) -> Auto:
    """Close the goal automatically: tries rfl, ring, norm_num, simp, linarith, positivity,
    nlinarith (with ``hints``), field_simp, aesop (and ``exact?`` if ``library_search``).
    """
    return Auto(hints=_terms(hints), aesop=aesop, library_search=library_search,
                origin=caller_origin())


def have(name: str, prop: object, proof: Tactic | None = None) -> Have:
    """``have name : prop`` proved by ``proof`` (default: ``pl.auto()``)."""
    from .expr import _as_prop

    validate_identifier(name, "have name")
    return Have(name=name, prop=_as_prop(prop, f"have {name}"),
                proof=_proof_arg(proof, f"have {name}"), origin=caller_origin())


def calc(first: object, *chain: object) -> Calc:
    """``pl.calc(a, "=", b, "≤", c, by=...)`` style chains:

        pl.calc(a, ("=", b), ("<=", c, pl.nlinarith(...)))

    Each link is ``(relation, next_term)`` or ``(relation, next_term, proof)``; missing
    proofs default to ``pl.auto()``. Relations: = ≠ < ≤ > ≥ (or ASCII forms).
    """
    from .expr import _lift

    links = []
    for link in chain:
        if not isinstance(link, tuple) or len(link) not in (2, 3):
            raise TacticError("calc links are (relation, term) or (relation, term, proof)")
        rel = CALC_RELATIONS.get(link[0])
        if rel is None:
            raise TacticError(f"unknown calc relation {link[0]!r}")
        proof = _proof_arg(link[2], "calc step") if len(link) == 3 else None
        links.append((rel, _lift(link[1]), proof))
    if not links:
        raise TacticError("calc needs at least one link")
    return Calc(first=_lift(first), links=tuple(links), origin=caller_origin())


def show(prop: object) -> Show:
    """``show prop``: Lean checks the goal is (definitionally) ``prop``."""
    from .expr import _as_prop

    return Show(prop=_as_prop(prop, "show"), origin=caller_origin())


def obtain(names: str | Iterable[str], source: TermLike) -> Obtain:
    """``obtain ⟨x, hx⟩ := source`` (names space-separated or a list)."""
    ns = names.split() if isinstance(names, str) else list(names)
    return Obtain(names=_names(ns), source=_term(source), origin=caller_origin())


def cases(source: TermLike, *alternatives: str | Iterable[str]) -> Cases:
    """``rcases source with a | b``; each alternative may bind several names ("x hx")."""
    alts = tuple(_names(a.split() if isinstance(a, str) else list(a)) for a in alternatives)
    if len(alts) < 1:
        raise TacticError("cases needs at least one alternative")
    return Cases(source=_term(source), alternatives=alts, origin=caller_origin())


def induction(var: str, zero: Tactic | None = None, succ: Tactic | None = None, *,
              names: tuple[str, str] = ("k", "ih")) -> Induction:
    """Induction on a natural-number variable; cases default to ``pl.auto()``."""
    validate_identifier(var, "induction variable")
    return Induction(var=var, zero=_proof_arg(zero, "induction zero case"),
                     succ=_proof_arg(succ, "induction succ case"),
                     succ_names=_names(names), origin=caller_origin())  # type: ignore[arg-type]


def unfold(*defs: object) -> Unfold:
    """``unfold f``: expand PyLeanX/Lean definitions (pass definitions or names)."""
    out: list[str] = []
    for d in defs:
        out.append(str(getattr(d, "name", d)))
    for n in out:
        validate_qualified_name(n, "definition name")
    return Unfold(names=tuple(out), origin=caller_origin())


def ext(*names: str) -> Ext:
    """``ext i``: reduce an equality of functions or vectors to coordinates."""
    return Ext(names=_names(names), origin=caller_origin())


def proof(*steps_: Tactic) -> Tactic:
    """A proof as a sequence of steps (``pl.proof(pl.claim(...), pl.conclude(...))``).

    Steps are named ``step1``, ``step2``, … by position when the theorem is proved
    (nested blocks: ``step3_1``, …), and steps after a ``pl.let`` may see through that
    definition. A block ending in a :func:`chain` concludes with it.
    """
    out = list(steps_)
    for x in out:
        if not isinstance(x, Tactic):
            raise TacticError(f"pl.proof takes proof steps (pl.claim, …), got {x!r}")
    if not out:
        raise TacticError("pl.proof needs at least one step")
    if isinstance(out[-1], Chain):
        out.append(Conclude(origin=out[-1].origin))
    return steps(*out) if len(out) != 1 else out[0]


def _facts(because: object) -> tuple[Term, ...]:
    if because is None:
        return ()
    items = list(because) if isinstance(because, (list, tuple)) else [because]
    out: list[Term] = []
    for f in items:
        if isinstance(f, Claim):
            if not f.name:
                raise TacticError("to cite a claim, give it a name: pl.claim(..., name='h')")
            out.append(Name(f.name))
        elif isinstance(f, Let):
            out.append(Name(f.eq_name))
        else:
            out.append(_term(f))
    return tuple(out)


def claim(prop: object, because: object = None, *, name: str = "", note: str = "",
          proof: Tactic | None = None) -> Claim:
    """One step of a written proof: ``prop`` holds ``because`` of the cited facts.

    ``because`` is a fact or a list of facts: library lemmas (``an.chain_rule``,
    ``pl.mathlib.…``), hypotheses (``"h"`` or ``pl.hyp("h")``), earlier named claims,
    or other theorems. Earlier claims are always available and need not be cited.
    ``note`` is the human reason shown when the proof is printed (``"by AA"``).
    Lean fills the routine gap between the cited facts and ``prop`` with standard
    automation; give ``proof=`` to close the step with an explicit tactic instead.
    """
    from .expr import _as_prop

    if name:
        validate_identifier(name, "claim name")
    if not isinstance(note, str):
        raise TacticError("claim note must be a string")
    return Claim(prop=_as_prop(prop, "claim"), facts=_facts(because), name=name, note=note,
                 proof=_proof_arg(proof, "claim"), origin=caller_origin())


def conclude(because: object = None, *, note: str = "",
             proof: Tactic | None = None) -> Conclude:
    """The final step of a written proof: the theorem's goal follows from ``because``
    and the claims so far (Lean fills the routine gap)."""
    if not isinstance(note, str):
        raise TacticError("conclude note must be a string")
    return Conclude(facts=_facts(because), note=note, proof=_proof_arg(proof, "conclude"),
                    origin=caller_origin())


def let(var: object, value: object, *, note: str = "") -> Let:
    """``Let f = value`` inside a proof. ``var`` is a symbol (``pl.symbol("f",
    pl.Fn(pl.Real, pl.Real))``); ``value`` an expression or a Python function
    (``lambda t: sin(t)**2 + cos(t)**2``) of the symbol's argument sorts."""
    from .expr import _lift
    from .types import LeanType

    if not isinstance(var, Var):
        raise TacticError("pl.let needs a symbol to name, e.g. pl.symbol('f', pl.Fn(...))")
    if callable(value) and not isinstance(value, Expr):
        from .terms import fun

        sort = var.sort
        if not (isinstance(sort, LeanType) and sort.kind == "fn"):
            raise TacticError(f"pl.let({var.name}, lambda …) needs a function-sorted symbol")
        value = fun(value, list(sort.parts[:-1]))
    return Let(var=var, value=_lift(value), note=note, origin=caller_origin())


# =====================================================================================
# More written-proof moves: let x be arbitrary, take, choose, contradiction, cases,
# induction, chains of (in)equalities, "it suffices to show"
# =====================================================================================

_CONTRA_IMPORTS = ("Mathlib.Tactic.ByContra",)


@dataclass(frozen=True)
class _Justified(Tactic):
    """A step whose statement is closed by :class:`Justify` from cited facts."""

    facts: tuple[Term, ...] = ()
    note: str = ""
    unfold: tuple[str, ...] = ()
    avoid: tuple[str, ...] = field(default=(), compare=False)

    def justification(self) -> Tactic:
        return Justify(self.facts, self.unfold, self.avoid)

    def imports(self) -> tuple[str, ...]:
        return self.justification().imports()


@dataclass(frozen=True)
class Fix(Tactic):
    """*Let x be arbitrary* / *assume P*: ``intro x (h : P)`` on a ∀ or ⇒ goal."""

    vars: tuple[Var, ...] = ()
    hyps: tuple[tuple[str, Expr], ...] = ()
    note: str = ""

    def imports(self) -> tuple[str, ...]:
        from .imports import expr_imports

        return tuple(i for _, p in self.hyps for i in expr_imports(p))

    def canonical(self) -> Any:
        return ["fix", [v.canonical() for v in self.vars],
                [[n, p.canonical()] for n, p in self.hyps], self.note]


@dataclass(frozen=True)
class Take(Tactic):
    """*Take x = w*: provide the witness of an ∃ goal (``refine ⟨w, ?_⟩``)."""

    witnesses: tuple[Expr, ...] = ()
    note: str = ""

    def imports(self) -> tuple[str, ...]:
        from .imports import expr_imports

        return tuple(i for w in self.witnesses for i in expr_imports(w))

    def canonical(self) -> Any:
        return ["take", [w.canonical() for w in self.witnesses], self.note]


@dataclass(frozen=True)
class Choose(_Justified):
    """*Choose x with P(x)*: ``obtain ⟨x, h⟩ : ∃ x, P x := by …`` from the cited facts."""

    vars: tuple[Var, ...] = ()
    prop: Expr = None  # type: ignore[assignment]
    names: tuple[str, ...] = ()

    def statement(self) -> Expr:
        from .expr import Exists

        return Exists(list(self.vars), self.prop)

    def canonical(self) -> Any:
        return ["choose", [v.canonical() for v in self.vars], self.prop.canonical(),
                list(self.names), [_canon_term(t) for t in self.facts], self.note,
                list(self.unfold)]


@dataclass(frozen=True)
class SupposeNot(Tactic):
    """*Suppose, for contradiction, that P*: ``by_contra``; the goal becomes ``False``.

    ``prop`` is the assumption as the mathematician states it (``p ≤ n`` for the goal
    ``n < p``); Lean checks it follows from the negated goal. ``None`` means "¬ goal".
    """

    prop: Expr | None = None
    name: str = "h"
    note: str = ""
    IMPORTS = _CONTRA_IMPORTS

    def canonical(self) -> Any:
        return ["suppose_not", self.prop.canonical() if self.prop is not None else None,
                self.name, self.note]


@dataclass(frozen=True)
class Case:
    """One case of a case split: its assumption and the proof in that case."""

    prop: Expr
    body: Tactic
    name: str = "h"
    note: str = ""

    def canonical(self) -> Any:
        return [self.prop.canonical(), self.body.canonical(), self.name, self.note]


@dataclass(frozen=True)
class CaseSplit(_Justified):
    """*Either P₁ or P₂ (or …)*: prove the disjunction from the facts, then each case."""

    cases: tuple[Case, ...] = ()
    name: str = ""

    def disjunction(self) -> Expr:
        from .expr import Or

        return Or(*(c.prop for c in self.cases))

    def sub_tactics(self) -> tuple[Tactic, ...]:
        return tuple(c.body for c in self.cases)

    def imports(self) -> tuple[str, ...]:
        return (*super().imports(), *(i for c in self.cases for i in c.body.imports()))

    def canonical(self) -> Any:
        return ["case_split", [c.canonical() for c in self.cases],
                [_canon_term(t) for t in self.facts], self.note, self.name, list(self.unfold)]


@dataclass(frozen=True)
class InductionOn(Tactic):
    """Induction on a natural number: base case 0, then from ``k`` to ``k + 1``."""

    var: Var = None  # type: ignore[assignment]
    base: Tactic = None  # type: ignore[assignment]
    step: Tactic = None  # type: ignore[assignment]
    k: Var = None  # type: ignore[assignment]
    ih: str = "ih"
    note: str = ""

    def sub_tactics(self) -> tuple[Tactic, ...]:
        return (self.base, self.step)

    def imports(self) -> tuple[str, ...]:
        return (*self.base.imports(), *self.step.imports())

    def canonical(self) -> Any:
        return ["induction_on", self.var.canonical(), self.base.canonical(),
                self.step.canonical(), self.k.canonical(), self.ih, self.note]


_REL_OPS = {"=": "eq", "≤": "le", "<": "lt", "≥": "ge", ">": "gt"}


def chain_relation(rels: Iterable[str]) -> str:
    """The relation a chain proves: ``=`` and ``≤`` give ``≤``, any ``<`` gives ``<``."""
    rs = set(rels)
    if rs <= {"="}:
        return "="
    if rs <= {"=", "≤", "<"}:
        return "<" if "<" in rs else "≤"
    if rs <= {"=", "≥", ">"}:
        return ">" if ">" in rs else "≥"
    raise TacticError(f"a chain cannot mix the relations {sorted(rs)}")


@dataclass(frozen=True)
class Chain(Tactic):
    """``a = b ≤ c < d``, each link with its own reason (Lean: a ``calc`` block)."""

    first: Expr = None  # type: ignore[assignment]
    links: tuple[tuple[str, Expr, tuple[Term, ...], str], ...] = ()
    name: str = ""
    unfold: tuple[str, ...] = ()
    avoid: tuple[str, ...] = field(default=(), compare=False)

    def relation(self) -> str:
        return chain_relation(r for r, _, _, _ in self.links)

    def statement(self) -> Expr:
        from .expr import _compare

        return _compare(_REL_OPS[self.relation()], self.first, self.links[-1][1])

    def as_calc(self) -> Calc:
        return Calc(first=self.first, links=tuple(
            (r, e, Justify(f, self.unfold, self.avoid)) for r, e, f, _ in self.links))

    def imports(self) -> tuple[str, ...]:
        return self.as_calc().imports()

    def sub_tactics(self) -> tuple[Tactic, ...]:
        return ()

    def canonical(self) -> Any:
        return ["chain", self.name, self.first.canonical(),
                [[r, e.canonical(), [_canon_term(t) for t in f], n]
                 for r, e, f, n in self.links], list(self.unfold)]


@dataclass(frozen=True)
class Suffices(_Justified):
    """*It suffices to show P*: the goal follows from P (by the facts); then prove P."""

    prop: Expr = None  # type: ignore[assignment]
    name: str = "h"

    def canonical(self) -> Any:
        return ["suffices", self.prop.canonical(), self.name,
                [_canon_term(t) for t in self.facts], self.note, list(self.unfold)]


def _block_arg(body: object, what: str) -> Tactic:
    if isinstance(body, Tactic):
        return body
    if isinstance(body, (list, tuple)) and body and all(isinstance(b, Tactic) for b in body):
        return proof(*body)
    raise TacticError(f"{what}: give the proof steps (a list of pl.claim(...), …)")


def _vars(vs: object, what: str) -> tuple[Var, ...]:
    items = list(vs) if isinstance(vs, (list, tuple)) else [vs]
    if not items or not all(isinstance(v, Var) for v in items):
        raise TacticError(f"{what} takes symbols (pl.symbol / pl.symbols)")
    return tuple(items)  # type: ignore[arg-type]


def _named_props(given: object, default: str, what: str) -> tuple[tuple[str, Expr], ...]:
    from .expr import _as_prop

    if given is None:
        return ()
    if isinstance(given, dict):
        out = []
        for k, v in given.items():
            validate_identifier(k, f"{what} hypothesis name")
            out.append((k, _as_prop(v, what)))
        return tuple(out)
    items = list(given) if isinstance(given, (list, tuple)) else [given]
    names = [default] if len(items) == 1 else [f"{default}{i}" for i in range(1, len(items) + 1)]
    return tuple((n, _as_prop(v, what)) for n, v in zip(names, items, strict=True))


def fix(*variables: Var, assume: object = None, note: str = "") -> Fix:
    """*Let x be arbitrary* (and *assume P*): introduces the ∀-variables of the goal and,
    with ``assume``, its hypotheses. ``assume`` is a proposition (named ``h``) or a dict
    ``{"hε": eps > 0}``; Lean checks each one is exactly what the goal provides.

        pl.fix(eps, assume={"hε": eps > 0})        # Let ε > 0.
    """
    vs = _vars(list(variables), "pl.fix") if variables else ()
    hyps = _named_props(assume, "h", "pl.fix")
    if not vs and not hyps:
        raise TacticError("pl.fix needs variables or assume=")
    return Fix(vars=vs, hyps=hyps, note=note, origin=caller_origin())


def assume(prop: object, *, name: str = "h", note: str = "") -> Fix:
    """*Assume P* (on a goal ``P → Q``): introduce the hypothesis ``name : P``."""
    validate_identifier(name, "assumption name")
    return Fix(hyps=_named_props({name: prop}, name, "pl.assume"), note=note,
               origin=caller_origin())


def take(*witnesses: object, note: str = "") -> Take:
    """*Take x = w*: the witness(es) for an ∃ goal (``pl.take(eps / 2)``)."""
    from .expr import _lift

    if not witnesses:
        raise TacticError("pl.take needs a witness")
    return Take(witnesses=tuple(_lift(w) for w in witnesses), note=note,
                origin=caller_origin())


def choose(variables: object, such_that: object, because: object = None, *,
           names: str | Iterable[str] = "h", note: str = "") -> Choose:
    """*Choose x with P(x)* (by the cited facts): ``P`` may use the new variables, and
    ``names`` names its parts (``"hp hdiv"`` splits ``A ∧ B`` into two hypotheses)."""
    from .expr import _as_prop

    vs = _vars(variables, "pl.choose")
    ns = names.split() if isinstance(names, str) else list(names)
    if not ns:
        raise TacticError("pl.choose needs a name for the chosen property")
    for n in ns:
        validate_identifier(n, "pl.choose name")
    return Choose(vars=vs, prop=_as_prop(such_that, "pl.choose"), names=tuple(ns),
                  facts=_facts(because), note=note, origin=caller_origin())


def suppose_not(prop: object = None, *, name: str = "h", note: str = "") -> SupposeNot:
    """*Suppose, for contradiction, that P*. ``prop`` is the assumption in your words
    (``p <= n`` when proving ``n < p``); omit it for "suppose the claim is false".
    The rest of the block must reach a contradiction (``pl.conclude(because=…)``)."""
    from .expr import _as_prop

    validate_identifier(name, "pl.suppose_not name")
    return SupposeNot(prop=_as_prop(prop, "pl.suppose_not") if prop is not None else None,
                      name=name, note=note, origin=caller_origin())


def case(prop: object, *body: Tactic, name: str = "h", note: str = "") -> Case:
    """One case for :func:`cases_on`: ``pl.case(n_even, step, step, …)``."""
    from .expr import _as_prop

    validate_identifier(name, "case name")
    return Case(prop=_as_prop(prop, "pl.case"), body=_block_arg(list(body), "pl.case"),
                name=name, note=note)


def cases_on(*cases_: Case, because: object = None, note: str = "") -> CaseSplit:
    """*Either P₁ or P₂*: split into cases. ``because`` proves ``P₁ ∨ P₂ ∨ …``
    (e.g. ``nt.even_or_odd``); two cases ``P``, ``¬P`` need no reason."""
    from .expr import NotP

    if len(cases_) < 2 or not all(isinstance(c, Case) for c in cases_):
        raise TacticError("pl.cases_on needs at least two pl.case(...)")
    facts = _facts(because)
    second = cases_[1].prop
    if not facts and len(cases_) == 2 and isinstance(second, NotP) \
            and second.arg._key() == cases_[0].prop._key():
        facts = (Name("Classical.em", label="either P or not P"),)
    return CaseSplit(cases=tuple(cases_), facts=facts, note=note, origin=caller_origin())


def induction_on(n: Var, *, base: object, step: object, k: Var | None = None,
                 ih: str = "ih", note: str = "") -> InductionOn:
    """Induction on the natural number ``n``: ``base`` proves the claim for 0, ``step``
    proves it for ``k + 1`` assuming it for ``k`` (hypothesis ``ih``)."""
    from .expr import make_var

    if not isinstance(n, Var):
        raise TacticError("pl.induction_on needs the variable to induct on")
    validate_identifier(ih, "induction hypothesis name")
    kv = k if k is not None else make_var("k", n.sort)
    return InductionOn(var=n, base=_block_arg(base, "base case"),
                       step=_block_arg(step, "inductive step"), k=kv, ih=ih, note=note,
                       origin=caller_origin())


def chain(first: object, *links: object, name: str = "") -> Chain:
    """``a = b ≤ c``, each link ``(relation, term)``, ``(relation, term, because)`` or
    ``(relation, term, because, note)``. Relations: = ≤ < ≥ > (or ASCII). As the last step
    of a block it proves the goal; otherwise it is a claim (``first`` R ``last``)."""
    from .expr import _lift

    out = []
    for link in links:
        if not isinstance(link, tuple) or len(link) not in (2, 3, 4):
            raise TacticError("chain links are (relation, term[, because[, note]])")
        rel = CALC_RELATIONS.get(link[0])
        if rel is None or rel == "≠":
            raise TacticError(f"unknown chain relation {link[0]!r}")
        because = link[2] if len(link) > 2 else None
        note = link[3] if len(link) > 3 else ""
        if not isinstance(note, str):
            raise TacticError("a chain link's note must be a string")
        out.append((rel, _lift(link[1]), _facts(because), note))
    if not out:
        raise TacticError("pl.chain needs at least one link")
    chain_relation(r for r, _, _, _ in out)
    if name:
        validate_identifier(name, "chain name")
    return Chain(first=_lift(first), links=tuple(out), name=name, origin=caller_origin())


def suffices(prop: object, because: object = None, *, name: str = "h",
             note: str = "") -> Suffices:
    """*It suffices to show P*: the goal follows from ``P`` and ``because``; the rest of
    the block proves ``P``."""
    from .expr import _as_prop

    validate_identifier(name, "pl.suffices name")
    return Suffices(prop=_as_prop(prop, "pl.suffices"), name=name, facts=_facts(because),
                    note=note, origin=caller_origin())


# =====================================================================================
# Preparing a written proof: step names, visible definitions, avoided lemmas
# =====================================================================================


def _flatten(t: Tactic) -> list[Tactic]:
    if isinstance(t, Steps):
        return [x for s in t.tactics for x in _flatten(s)]
    return [t]


def prepare(t: Tactic, avoid: tuple[str, ...] = (), *, prefix: str = "step",
            lets: tuple[str, ...] = ()) -> Tactic:
    """Name unnamed steps by position (``step2``; nested blocks ``step2_1``), let later
    steps see through ``pl.let`` definitions, and pass ``avoid`` to every gap-filling
    step. Idempotent; run by ``Theorem.prove``."""
    from dataclasses import replace

    out: list[Tactic] = []
    pos = 0
    seen = tuple(lets)
    for s in _flatten(t):
        if not isinstance(s, Conclude):
            pos += 1
        here = f"{prefix}{pos}"
        if isinstance(s, Let):
            seen = (*seen, s.eq_name)
        elif isinstance(s, Claim):
            name = s.name or here
            sub = prepare(s.proof, avoid, prefix=f"{name}_", lets=seen) if s.proof else None
            s = replace(s, name=name, unfold=seen, avoid=avoid, proof=sub)
        elif isinstance(s, Conclude):
            sub = (prepare(s.proof, avoid, prefix=f"{prefix}end_", lets=seen)
                   if s.proof else None)
            s = replace(s, unfold=seen, avoid=avoid, proof=sub)
        elif isinstance(s, Chain):
            s = replace(s, name=s.name or here, unfold=seen, avoid=avoid)
        elif isinstance(s, CaseSplit):
            cs = tuple(replace(c, body=prepare(c.body, avoid, prefix=f"{here}c{i}_",
                                               lets=seen))
                       for i, c in enumerate(s.cases, start=1))
            s = replace(s, cases=cs, name=s.name or here, unfold=seen, avoid=avoid)
        elif isinstance(s, InductionOn):
            s = replace(s, base=prepare(s.base, avoid, prefix=f"{here}b_", lets=seen),
                        step=prepare(s.step, avoid, prefix=f"{here}i_", lets=seen))
        elif isinstance(s, (Choose, Suffices)):
            s = replace(s, unfold=seen, avoid=avoid)
        elif isinstance(s, Justify):
            s = replace(s, avoid=avoid)
        elif isinstance(s, Branches):
            s = replace(s, branches=tuple(
                prepare(b, avoid, prefix=f"{here}_{i}_", lets=seen)
                for i, b in enumerate(s.branches, start=1)))
        out.append(s)
    if len(out) == 1 and not isinstance(t, Steps):
        return out[0]
    return Steps(tactics=tuple(out), origin=t.origin)


# =====================================================================================
# Walking the terms a proof cites
# =====================================================================================


def iter_terms(t: Tactic | None) -> Iterable[Term]:
    """Every lemma/hypothesis/expression term a tactic tree refers to."""
    if t is None:
        return
    direct: list[Term] = []
    if isinstance(t, _WithLemmas):
        direct += list(t.lemmas)
    elif isinstance(t, (Exact, Apply)):
        direct.append(t.term)
    elif isinstance(t, Rewrite):
        direct += [r for r, _ in t.rules]
    elif isinstance(t, (Obtain, Cases)):
        direct.append(t.source)
    elif isinstance(t, Auto):
        direct += list(t.hints)
    elif isinstance(t, (Claim, Conclude, Justify, _Justified)):
        direct += list(t.facts)
    elif isinstance(t, Chain):
        direct += [f for _, _, fs, _ in t.links for f in fs]
    for term in direct:
        yield from _subterms(term)
    for s in t.sub_tactics():
        yield from iter_terms(s)


def _subterms(t: Term) -> Iterable[Term]:
    yield t
    if isinstance(t, TermApp):
        yield t.fn
        for a in t.args:
            yield from _subterms(a)


def library_facts(theorems: Iterable[Any]) -> list[LibraryFact]:
    """Shipped facts cited by ``theorems``, each once, dependencies first."""
    order: list[LibraryFact] = []
    seen: set[str] = set()

    def visit(f: LibraryFact) -> None:
        if f.name in seen:
            return
        seen.add(f.name)
        for r in f.requires:
            visit(r)
        order.append(f)

    for thm in theorems:
        for term in iter_terms(thm.proof):
            if isinstance(term, LibraryFact):
                visit(term)
    return order

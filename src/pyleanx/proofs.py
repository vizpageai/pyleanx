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

_JUSTIFY_IMPORTS = (*_AUTO_IMPORTS, "Aesop", "Mathlib.Tactic.FunProp")


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
        close = "first | assumption | rfl | fun_prop | positivity | linarith | (simp_all; done)"
        alts = ["assumption"]
        alts += [f"exact {f}" for f in fs]
        alts += [f"(apply {f}; all_goals ({close}))" for f, t in zip(fs, self.facts, strict=True)
                 if not isinstance(t, Expr)]
        alts += ["rfl", "ring1", "positivity", "fun_prop", f"linarith{h}",
                 f"(norm_num{hs}; done)", f"(simp{hs}; done)", f"(simp{hs}; ring1)",
                 f"nlinarith{h}", "(field_simp; ring1)", f"(simp_all{hs}; done)"]
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
    """Tell the gap-filling steps of a proof not to use the lemmas in ``avoid``."""
    from dataclasses import replace

    if not avoid:
        return t
    if isinstance(t, Steps):
        return replace(t, tactics=tuple(with_avoid(x, avoid) for x in t.tactics))
    if isinstance(t, Branches):
        return replace(t, branches=tuple(with_avoid(x, avoid) for x in t.branches))
    if isinstance(t, (Claim, Conclude, Justify)):
        return replace(t, avoid=avoid)
    return t


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

    Unnamed claims are named ``step1``, ``step2``, … by position, and claims after a
    ``pl.let`` may see through that definition.
    """
    from dataclasses import replace

    out: list[Tactic] = []
    lets: list[str] = []
    n = 0
    for s in steps_:
        if isinstance(s, Let):
            lets.append(s.eq_name)
        elif isinstance(s, Claim):
            n += 1
            s = replace(s, name=s.name or f"step{n}", unfold=tuple(lets))
        elif isinstance(s, Conclude):
            s = replace(s, unfold=tuple(lets))
        out.append(s)
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
    elif isinstance(t, (Claim, Conclude, Justify)):
        direct += list(t.facts)
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

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
from .expr import Expr
from .names import validate_identifier, validate_qualified_name

# =====================================================================================
# Proof terms (arguments of exact / apply / rw / simp)
# =====================================================================================


@dataclass(frozen=True)
class Name:
    """A hypothesis or library declaration referenced by (qualified) name."""

    name: str
    imports: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        validate_qualified_name(self.name, "lemma/hypothesis name")
        for imp in self.imports:
            validate_qualified_name(imp, "import module")

    def __call__(self, *args: TermLike) -> TermApp:
        return TermApp(self, tuple(_term(a) for a in args))

    def canonical(self) -> Any:
        return ["name", self.name]


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
    if isinstance(t, Name):
        return t.imports
    if isinstance(t, TermApp):
        out = list(t.fn.imports)
        for a in t.args:
            out.extend(term_imports(a))
        return tuple(out)
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
    return Ring(origin=caller_origin())


def omega() -> Omega:
    return Omega(origin=caller_origin())


def positivity() -> Positivity:
    return Positivity(origin=caller_origin())


def rfl() -> Rfl:
    return Rfl(origin=caller_origin())


def decide() -> Decide:
    return Decide(origin=caller_origin())


def constructor() -> Constructor:
    return Constructor(origin=caller_origin())


def assumption() -> Assumption:
    return Assumption(origin=caller_origin())


def linarith(*lemmas: TermLike) -> Linarith:
    return Linarith(lemmas=_terms(lemmas), origin=caller_origin())


def nlinarith(*lemmas: TermLike) -> Nlinarith:
    return Nlinarith(lemmas=_terms(lemmas), origin=caller_origin())


def norm_num(*lemmas: TermLike) -> NormNum:
    return NormNum(lemmas=_terms(lemmas), origin=caller_origin())


def simp(*lemmas: TermLike, only: bool = False, at: str | Iterable[str] = ()) -> Simp:
    at_names = _names([at] if isinstance(at, str) else at)
    return Simp(lemmas=_terms(lemmas), only=only, at=at_names, origin=caller_origin())


def intro(*names: str) -> Intro:
    if not names:
        raise TacticError("intro needs at least one name (anonymous intro is not supported)")
    return Intro(names=_names(names), origin=caller_origin())


def exact(term: TermLike) -> Exact:
    return Exact(term=_term(term), origin=caller_origin())


def apply(term: TermLike) -> Apply:
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
    from .expr import _lift

    if not witnesses:
        raise TacticError("use needs at least one witness")
    return Use(witnesses=tuple(_lift(w) for w in witnesses), origin=caller_origin())


def steps(*tactics: Tactic) -> Steps:
    if not tactics:
        raise TacticError("steps() needs at least one tactic")
    for t in tactics:
        if not isinstance(t, Tactic):
            raise TacticError(f"steps() expects tactics, got {t!r}")
    return Steps(tactics=tuple(tactics), origin=caller_origin())


def branches(*proofs: Tactic) -> Branches:
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
    if isinstance(t, RawTactic):
        return True
    if isinstance(t, Steps):
        return any(contains_raw(x) for x in t.tactics)
    if isinstance(t, Branches):
        return any(contains_raw(x) for x in t.branches)
    return False


def iter_raw(t: Tactic) -> Iterable[RawTactic]:
    if isinstance(t, RawTactic):
        yield t
    elif isinstance(t, Steps):
        for x in t.tactics:
            yield from iter_raw(x)
    elif isinstance(t, Branches):
        for x in t.branches:
            yield from iter_raw(x)

"""Sort (type) descriptors and the explicit compatibility rules between them.

These are *descriptors* of Lean types, not Python numeric types. PyLeanX never
inserts coercions silently; the only conversions are the explicit embeddings
allowed by :func:`can_cast`.
"""

from __future__ import annotations

from dataclasses import dataclass

__all__ = ["Sort", "Nat", "Int", "Rat", "Real", "Prop", "NUMERIC_SORTS", "can_cast", "LeanType",
           "lean_type", "Fn", "Prod", "Fin", "EuclideanSpace", "UNKNOWN", "TYPE",
           "type_param"]


@dataclass(frozen=True)
class Sort:
    """A primitive Lean type known to PyLeanX."""

    name: str
    lean: str
    numeric: bool
    rank: int  # position in the embedding chain Nat -> Int -> Rat -> Real
    imports: tuple[str, ...] = ()
    unicode: str = ""  # Mathlib notation (ℝ, ℕ, ...) used when unicode_types=True
    unicode_imports: tuple[str, ...] = ()  # module that defines that notation
    latex: str = ""
    #: Opaque sorts are Lean types PyLeanX does not model: Python performs no sort checks on
    #: them and Lean's elaborator decides (see :class:`LeanType`).
    opaque: bool = False

    def lean_name(self, unicode: bool = False) -> str:
        return self.unicode if unicode and self.unicode else self.lean

    def canonical(self) -> object:
        return self.name

    @property
    def is_prop(self) -> bool:
        return self.name == "Prop"

    @property
    def allows_negation(self) -> bool:
        return self.numeric and self.name != "Nat"

    @property
    def allows_fractions(self) -> bool:
        return self.name in ("Rat", "Real")

    def __repr__(self) -> str:
        return f"pl.{self.name}"


Nat = Sort("Nat", "Nat", numeric=True, rank=0, unicode="ℕ",
           unicode_imports=("Mathlib.Data.Nat.Notation",), latex=r"\mathbb{N}")
Int = Sort("Int", "Int", numeric=True, rank=1, unicode="ℤ",
           unicode_imports=("Mathlib.Data.Int.Notation",), latex=r"\mathbb{Z}")
Rat = Sort("Rat", "Rat", numeric=True, rank=2, imports=("Mathlib.Data.Rat.Defs",), unicode="ℚ",
           unicode_imports=("Mathlib.Data.Rat.Init",), latex=r"\mathbb{Q}")
Real = Sort("Real", "Real", numeric=True, rank=3, imports=("Mathlib.Basic.Real.Basic",),
            unicode="ℝ", latex=r"\mathbb{R}")
Prop = Sort("Prop", "Prop", numeric=False, rank=-1, latex=r"\mathrm{Prop}")

NUMERIC_SORTS = (Nat, Int, Rat, Real)

#: Sorts by name, for deserialising canonical theorems (domain modules register theirs).
SORTS: dict[str, Sort] = {s.name: s for s in (Nat, Int, Rat, Real, Prop)}


def register_sort(sort: Sort) -> Sort:
    existing = SORTS.get(sort.name)
    if existing is not None and existing != sort:
        raise ValueError(f"a different sort named {sort.name!r} is already registered")
    SORTS[sort.name] = sort
    return sort


# =====================================================================================
# Open Lean types (checked by Lean, not by Python)
# =====================================================================================

_FORBIDDEN_TYPE_TOKENS = (":=", "#", "--", "/-", "set_option", "axiom", "sorry", "admit",
                          "macro", "elab", "syntax", "notation", "instance", "attribute")
_PAIRS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}


def validate_type_text(text: str) -> str:
    """Reject Lean type text that could escape its binder or add commands.

    Type text is spliced into generated Lean (``(x : <text>)``). It must be one line with
    balanced brackets and none of the command/escape tokens; Lean still elaborates it.
    """
    from .errors import IdentifierError

    if not isinstance(text, str) or not text.strip():
        raise IdentifierError("Lean type text must be a non-empty string")
    if any(ord(c) < 32 or ord(c) == 127 for c in text):
        raise IdentifierError(f"Lean type text {text!r} contains control characters/newlines")
    low = text.lower()
    for tok in _FORBIDDEN_TYPE_TOKENS:
        if tok in low:
            raise IdentifierError(f"Lean type text {text!r} contains forbidden token {tok!r}")
    stack: list[str] = []
    for c in text:
        if c in _PAIRS:
            stack.append(_PAIRS[c])
        elif c in _PAIRS.values():
            if not stack or stack.pop() != c:
                raise IdentifierError(f"Lean type text {text!r} has unbalanced brackets")
    if stack:
        raise IdentifierError(f"Lean type text {text!r} has unbalanced brackets")
    return text.strip()


@dataclass(frozen=True)
class LeanType(Sort):
    """Any Lean type, e.g. ``EuclideanSpace ℝ (Fin 3)``, ``ℝ → ℝ``, a library structure.

    PyLeanX does not type-check terms of these sorts itself (``opaque=True``): operators and
    comparisons are passed through and Lean's elaborator accepts or rejects them, with the
    error mapped back to the Python line. Instances are interned, so ``is`` works.
    """

    kind: str = "type"  # type | fn | prod | struct
    parts: tuple[Sort, ...] = ()  # fn: domains..., codomain; prod: components
    fields: tuple[tuple[str, Sort], ...] = ()  # struct fields (name, sort)
    definitions: tuple[object, ...] = ()  # PyLeanX definitions this type depends on
    classes: tuple[str, ...] = ()  # param: the structure it carries (``Group``)
    label: str = ""  # param: the structure in words ("group")

    def lean_name(self, unicode: bool = False) -> str:
        if self.kind == "fn":
            *dom, cod = self.parts
            return " → ".join([*(_wrap(d, unicode, ("fn",)) for d in dom),
                               _wrap(cod, unicode, ())])
        if self.kind == "prod":
            return " × ".join(_wrap(p, unicode, ("fn", "prod")) for p in self.parts)
        return self.lean

    def canonical(self) -> object:
        if self.kind == "fn":
            return ["fn", [p.canonical() for p in self.parts]]
        if self.kind == "prod":
            return ["prod", [p.canonical() for p in self.parts]]
        if self.kind == "param":
            return ["param", self.lean, list(self.classes), list(self.imports), self.label]
        if self.definitions:
            return ["type", self.lean, list(self.imports),
                    [getattr(d, "name", "?") for d in self.definitions]]
        return ["type", self.lean, list(self.imports)]

    def field_sort(self, name: str) -> Sort | None:
        return dict(self.fields).get(name)

    def __repr__(self) -> str:
        return f"pl.LeanType({self.lean_name()!r})"


def _wrap(s: Sort, unicode: bool, paren_kinds: tuple[str, ...]) -> str:
    text = s.lean_name(unicode)
    return f"({text})" if isinstance(s, LeanType) and s.kind in paren_kinds else text


_INTERN: dict[tuple, LeanType] = {}


def _intern(t: LeanType) -> LeanType:
    key = (t.name, t.kind, t.parts, t.imports, t.latex, t.fields, t.definitions,
           t.classes, t.label)
    return _INTERN.setdefault(key, t)


def lean_type(text: str, imports: tuple[str, ...] | list[str] = (), *, latex: str = "",
              fields: tuple[tuple[str, Sort], ...] = (),
              definitions: tuple[object, ...] = ()) -> LeanType:
    """An arbitrary Lean type given as Lean text (validated, then checked by Lean)."""
    from .names import validate_qualified_name

    text = validate_type_text(text)
    imps = tuple(validate_qualified_name(i, "import module") for i in imports)
    return _intern(LeanType(text, text, numeric=False, rank=-2, imports=imps, latex=latex,
                            opaque=True, kind="struct" if fields else "type",
                            fields=tuple(fields), definitions=tuple(definitions)))


def _compound(kind: str, sorts: tuple[Sort, ...]) -> LeanType:
    imps = tuple(sorted({i for s in sorts for i in s.imports}))
    tmp = LeanType("", "", numeric=False, rank=-2, opaque=True, kind=kind, parts=sorts)
    text = tmp.lean_name()
    defs: list[object] = []
    for s in sorts:
        for d in getattr(s, "definitions", ()):
            if d not in defs:
                defs.append(d)
    return _intern(LeanType(text, text, numeric=False, rank=-2, imports=imps, opaque=True,
                            kind=kind, parts=sorts, definitions=tuple(defs)))


def Fn(*sorts: Sort) -> LeanType:  # noqa: N802 - type constructor
    """Function type ``A → B`` (``Fn(A, B, C)`` is ``A → B → C``)."""
    if len(sorts) < 2 or not all(isinstance(s, Sort) for s in sorts):
        raise TypeError("pl.Fn needs at least two sorts, e.g. pl.Fn(pl.Real, pl.Real)")
    return _compound("fn", tuple(sorts))


def Prod(*sorts: Sort) -> LeanType:  # noqa: N802
    """Product type ``A × B`` (pairs ``pl.pair(a, b)``, projections ``p.fst``/``p.snd``)."""
    if len(sorts) < 2 or not all(isinstance(s, Sort) for s in sorts):
        raise TypeError("pl.Prod needs at least two sorts")
    return _compound("prod", tuple(sorts))


def Fin(n: int) -> LeanType:  # noqa: N802
    """``Fin n``: the numbers 0, …, n-1 (indices of coordinates)."""
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise TypeError("pl.Fin needs a non-negative int")
    return lean_type(f"Fin {n}", latex=rf"\mathrm{{Fin}}\,{n}")


def EuclideanSpace(n: int) -> LeanType:  # noqa: N802
    """``EuclideanSpace ℝ (Fin n)``: ℝⁿ with the Euclidean norm and inner product."""
    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        raise TypeError("pl.EuclideanSpace needs a positive int")
    return lean_type(f"EuclideanSpace ℝ (Fin {n})",
                     ("Mathlib.Analysis.InnerProductSpace.PiL2",), latex=rf"\mathbb{{R}}^{{{n}}}")


def type_param(name: str, *classes: str, imports: tuple[str, ...] | list[str] = (),
               label: str = "", latex: str = "") -> LeanType:
    """An arbitrary type carrying a structure: *let G be a group*.

    ``G = pl.type_param("G", "Group", label="group")``; a theorem whose variables live in
    ``G`` is stated for every group (Lean: ``{G : Type*} [Group G]``). ``classes`` are
    Lean type classes applied to the type (``"Group"``, ``"Field"``, ``"Module ℝ"``).
    """
    from .names import validate_identifier, validate_qualified_name

    validate_identifier(name, "type parameter name")
    for c in classes:
        validate_type_text(f"{c} {name}")
    imps = ("Mathlib.Tactic.TypeStar",
            *(validate_qualified_name(i, "import module") for i in imports))
    return _intern(LeanType(name, name, numeric=False, rank=-2, imports=imps,
                            latex=latex or name, opaque=True, kind="param",
                            classes=tuple(classes), label=label))


def type_params(sorts: object) -> list[LeanType]:
    """The type parameters (:func:`type_param`) the given sorts mention, in order."""
    out: list[LeanType] = []

    def visit(s: object) -> None:
        if isinstance(s, LeanType):
            if s.kind == "param" and s not in out:
                out.append(s)
            for q in s.parts:
                visit(q)

    for s in sorts:  # type: ignore[attr-defined]
        visit(s)
    return out


#: The sort of terms whose type PyLeanX does not know (e.g. results of library functions).
UNKNOWN = _intern(LeanType("_", "_", numeric=False, rank=-2, opaque=True))
#: The sort of types used as terms (``fderiv ℝ f x`` passes ℝ as an argument).
TYPE = _intern(LeanType("Type", "Type", numeric=False, rank=-2, opaque=True))


def can_cast(src: Sort, dst: Sort) -> bool:
    """Only the canonical, meaning-preserving embeddings Nat -> Int -> Rat -> Real."""
    return src.numeric and dst.numeric and src.rank < dst.rank

"""Show a library declaration the way Lean's editor infoview does, without restating it.

    import pyleanx as pl
    pl.infoview(pl.algebra.two_mul_le_add_sq)

    α : Type u_1
    inst✝ : CommRing α
    ...
    a b : α
    ⊢ 2 * a * b ≤ a ^ 2 + b ^ 2

Lean prints the declaration (``#check name``, at the pinned toolchain and Mathlib);
PyLeanX only splits that signature into binders and the conclusion for layout. Nothing
here proves or verifies anything, and no ``sorry`` is involved.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass

from .errors import ProjectError
from .names import validate_qualified_name
from .proofs import Name

_CLOSE = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩"}
_KIND = {"(": "explicit", "{": "implicit", "[": "instance", "⦃": "strict implicit"}


@dataclass(frozen=True)
class Binder:
    names: str  # "a b", or "inst✝" for an anonymous instance
    type: str
    kind: str  # explicit | implicit | instance | strict implicit

    def __str__(self) -> str:
        return f"{self.names} : {self.type}"


@dataclass(frozen=True)
class DeclView:
    """A declaration as Lean printed it, laid out like the infoview's goal display."""

    name: str
    signature: str  # Lean's own `#check name` output (whitespace normalised)
    binders: tuple[Binder, ...]
    conclusion: str | None  # None if the signature could not be split (shown verbatim)

    @property
    def goal(self) -> str:
        """``hypotheses ⊢ conclusion``, as the infoview shows it after ``intro``."""
        if self.conclusion is None:
            return self.signature
        return "\n".join([*(str(b) for b in self.binders), f"⊢ {self.conclusion}"])

    def __str__(self) -> str:
        return self.goal

    def _repr_markdown_(self) -> str:  # Jupyter
        return (f"**`{self.name}`**\n\n```lean\n{self.goal}\n```\n\n"
                f"<details><summary>signature</summary>\n\n```lean\n{self.signature}\n```\n"
                "</details>")


class DeclViews(tuple):
    """Several :class:`DeclView`s; renders all of them in Jupyter."""

    def _repr_markdown_(self) -> str:
        return "\n\n---\n\n".join(v._repr_markdown_() for v in self)

    def __str__(self) -> str:
        return "\n\n".join(f"{v.name}\n{v.goal}" for v in self)


def _match(text: str, start: int) -> int:
    """Index of the bracket closing ``text[start]`` (nesting-aware), or -1."""
    stack = [_CLOSE[text[start]]]
    i = start + 1
    while i < len(text):
        c = text[i]
        if c in _CLOSE:
            stack.append(_CLOSE[c])
        elif stack and c == stack[-1]:
            stack.pop()
            if not stack:
                return i
        i += 1
    return -1


def _split_colon(group: str) -> tuple[str, str] | None:
    """Split ``names : type`` at the first top-level `` : ``."""
    depth = 0
    for i, c in enumerate(group):
        if c in _CLOSE:
            depth += 1
        elif c in _CLOSE.values():
            depth -= 1
        elif depth == 0 and group.startswith(" : ", i):
            return group[:i].strip(), group[i + 3:].strip()
    return None


def parse_signature(signature: str, name: str) -> tuple[tuple[Binder, ...], str | None]:
    """Split Lean's ``#check name`` output into binders and conclusion.

    Returns ``((), None)`` when the text does not have the expected shape; callers then
    show the signature verbatim.
    """
    text = " ".join(signature.split())
    if not text.startswith(name):
        return (), None
    rest = text[len(name):]
    if rest.startswith(".{"):  # universe parameters
        end = rest.find("}")
        if end < 0:
            return (), None
        rest = rest[end + 1:]
    binders: list[Binder] = []
    while True:
        rest = rest.lstrip()
        if rest.startswith(":"):
            return tuple(binders), rest[1:].strip()
        if not rest or rest[0] not in _KIND:
            return (), None
        end = _match(rest, 0)
        if end < 0:
            return (), None
        group, kind = rest[1:end].strip(), _KIND[rest[0]]
        rest = rest[end + 1:]
        split = _split_colon(group)
        if split is None:
            if kind != "instance":
                return (), None
            binders.append(Binder("inst✝", group, kind))
        else:
            binders.append(Binder(split[0], split[1], kind))


def _target(item: Name | str) -> tuple[str, tuple[str, ...]]:
    if isinstance(item, Name):
        return item.name, item.imports
    if isinstance(item, str):
        validate_qualified_name(item, "declaration name")
        return item, ()
    raise TypeError(f"expected a declaration name or pl.ref(...), got {item!r}")


def infoview(
    *items: Name | str,
    imports: Iterable[str] = (),
    project: object = None,
    timeout: float | None = None,
) -> DeclView | DeclViews:
    """Display Mathlib/core declarations infoview-style, as Lean states them.

    ``items`` are names (``"Nat.add_comm"``), ``pl.ref(...)`` or catalog lemmas
    (``pl.algebra.sq_nonneg``). Modules come from the references plus ``imports``;
    if none are known at all, ``import Mathlib`` is used (correct but slow to load).
    One Lean process checks all items. Returns one view, or a tuple for several items.
    """
    if not items:
        raise TypeError("infoview() needs at least one declaration")
    from .backend.declarations import check_declarations

    targets = [_target(i) for i in items]
    mods = {m for _, ms in targets for m in ms} | set(imports)
    if not mods:
        mods = {"Mathlib"}
    names = [n for n, _ in targets]
    infos = check_declarations(names, mods, project, timeout=timeout,  # type: ignore[arg-type]
                               signature=True)
    views = []
    for n in names:
        info = infos[n]
        if not info.exists or info.type is None:
            raise ProjectError(f"Lean does not know `{n}` with imports {sorted(mods)}: "
                               f"{info.error}")
        binders, concl = parse_signature(info.type, n)
        views.append(DeclView(n, " ".join(info.type.split()), binders, concl))
    return views[0] if len(views) == 1 else DeclViews(views)

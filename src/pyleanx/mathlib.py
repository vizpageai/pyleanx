"""A small, curated set of Mathlib lemma references with the imports they need.

Each entry is a typed :class:`~pyleanx.proofs.Name`; nothing here asserts a lemma's
statement -- Lean checks every use. Names are tied to the pinned Mathlib revision.
"""

from __future__ import annotations

from .proofs import Name

_ORDER_RING = "Mathlib.Algebra.Order.Ring.Unbundled.Basic"

sq_nonneg = Name("sq_nonneg", (_ORDER_RING,))
mul_self_nonneg = Name("mul_self_nonneg", (_ORDER_RING,))
add_comm = Name("add_comm")
mul_comm = Name("mul_comm")
add_assoc = Name("add_assoc")
mul_assoc = Name("mul_assoc")
Nat_add_zero = Name("Nat.add_zero")  # noqa: N816 - mirrors the Lean name
Nat_zero_add = Name("Nat.zero_add")  # noqa: N816
le_refl = Name("le_refl")
le_trans = Name("le_trans")
add_pos = Name("add_pos")
mul_pos = Name("mul_pos")

__all__ = [
    "sq_nonneg", "mul_self_nonneg", "add_comm", "mul_comm", "add_assoc", "mul_assoc",
    "Nat_add_zero", "Nat_zero_add", "le_refl", "le_trans", "add_pos", "mul_pos",
]


# =====================================================================================
# All of Mathlib (and Lean core / Batteries) by name: pl.mathlib.Real.sqrt_le_sqrt
# =====================================================================================
#
# Any attribute not defined above is looked up in an index of the pinned Mathlib sources
# (pyleanx.mathlib_index), so users never write module paths: PyLeanX imports exactly the
# module that defines each declaration. pl.ref(name, imports=[...]) keeps working.

import difflib as _difflib  # noqa: E402
from typing import Any as _Any  # noqa: E402

_CHILDREN: dict[str, dict[str, None]] = {}


def _index() -> dict[str, list[str]]:
    from .mathlib_index import load_index

    return load_index(progress=print)["names"]


def _children(prefix: str) -> dict[str, None]:
    if not _CHILDREN:
        tree: dict[str, dict[str, None]] = {}
        for full in _index():
            parts = full.split(".")
            for i in range(len(parts)):
                tree.setdefault(".".join(parts[:i]), {})[parts[i]] = None
        _CHILDREN.update(tree)
    return _CHILDREN.get(prefix, {})


def _imports(module: str) -> tuple[str, ...]:
    from .mathlib_index import CORE

    return () if module == CORE else (module,)


def find(name: str) -> tuple[str, str] | None:
    """(module, kind) of a Lean/Mathlib declaration, or None. kind: theorem | def | type."""
    hit = _index().get(name)
    return (hit[0], hit[1]) if hit else None


def search(text: str, limit: int = 30) -> list[str]:
    """Declaration names containing every word of ``text`` (case-insensitive)."""
    import re

    words = text.lower().replace("_", " ").split()
    in_order = re.compile(".*".join(map(re.escape, words)))
    hits = [n for n in _index() if all(w in n.lower() for w in words)]

    def rank(n: str) -> tuple[int, int, int, str]:
        last = n.rsplit(".", 1)[-1].lower()
        parts = set(last.split("_"))
        exact = sum(w in parts for w in words)  # whole words of the last component
        return (-exact, 0 if in_order.search(last) else 1, len(n), n)

    return sorted(hits, key=rank)[:limit]


class MathlibName:
    """A Lean/Mathlib namespace or declaration reached by attribute access.

    Theorems are citable lemmas (``M.sq_nonneg(x)``), definitions are terms
    (``M.Real.sqrt(x)``), types are sorts (``pl.var("v", M.EuclideanSpace(pl.Real,
    pl.Fin(3)))``); namespaces give access to their members.
    """

    __slots__ = ("_path",)

    def __init__(self, path: str) -> None:
        object.__setattr__(self, "_path", path)

    @property
    def name(self) -> str:
        return self._path

    @property
    def info(self) -> tuple[str, str] | None:
        return find(self._path) if self._path else None

    # -- navigation ---------------------------------------------------------------
    def __getattr__(self, attr: str) -> _Any:
        if attr.startswith("__"):
            raise AttributeError(attr)
        return _resolve(self._path, attr)

    def __dir__(self) -> list[str]:
        from .bindings import ascii_alias

        return sorted({ascii_alias(c) for c in _children(self._path)})

    def __repr__(self) -> str:
        info = self.info
        what = f"{info[1]} in {info[0]}" if info else "namespace"
        return f"<pl.mathlib {self._path or '(root)'}: {what}>"

    # -- conversions used by PyLeanX --------------------------------------------------
    def _decl(self) -> tuple[str, str]:
        info = self.info
        if info is None:
            raise AttributeError(f"{self._path} is a namespace, not a declaration")
        return info

    def __pyleanx_term__(self) -> _Any:
        module, kind = self._decl()
        if kind == "theorem":
            return Name(self._path, _imports(module))
        return self.__pyleanx_expr__()

    def __pyleanx_expr__(self) -> _Any:
        module, kind = self._decl()
        if kind == "type":
            from .terms import TypeTerm

            return TypeTerm(self.__pyleanx_sort__())
        from .terms import Const
        from .types import UNKNOWN

        return Const(self._path, UNKNOWN, _imports(module))

    def __pyleanx_sort__(self) -> _Any:
        module, _ = self._decl()
        from .types import lean_type

        return lean_type(self._path, _imports(module))

    def __call__(self, *args: object) -> _Any:
        module, kind = self._decl()
        if kind == "theorem":
            return Name(self._path, _imports(module))(*args)  # type: ignore[arg-type]
        from .terms import Const, apply
        from .types import UNKNOWN

        return apply(Const(self._path, UNKNOWN, _imports(module)), *args)


def _resolve(prefix: str, attr: str) -> _Any:
    from .bindings import ascii_alias

    kids = _children(prefix)
    real = attr if attr in kids else next((k for k in kids if ascii_alias(k) == attr), None)
    full = f"{prefix}.{real or attr}" if prefix else (real or attr)
    if real is None:
        close = _difflib.get_close_matches(attr, list(kids), n=5)
        raise AttributeError(
            f"no Lean/Mathlib declaration or namespace {full!r} in the pinned Mathlib"
            + (f"; did you mean {close}?" if close else "")
            + ". pl.ref(name, imports=[module]) works for anything else.")
    info = find(full)
    if info is not None and info[1] == "theorem" and not _children(full):
        return Name(full, _imports(info[0]))  # plain lemma: the usual citable reference
    return MathlibName(full)


def __getattr__(attr: str) -> _Any:  # module-level: pl.mathlib.<anything>
    if attr.startswith("__"):
        raise AttributeError(attr)
    return _resolve("", attr)

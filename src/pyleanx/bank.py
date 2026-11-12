"""Local theorem bank (M7): search, versioned declarations, reuse in proofs.

    bank = pl.TheoremBank.open()                 # ~/.pyleanx/bank.json (or PYLEANX_BANK)
    bank.index_catalogs()                        # asks Lean for the statements (one run)
    hit = bank.search("triangle inequality")[0]
    proof = pl.exact(bank.ref(hit.entry.id)(A, B, C))

Every entry separates its **canonical ID** (``geometry.triangle_inequality``: a bank
name, stable across renames) from the **Lean fully qualified name** (``dist_triangle``)
and records the exact formalization it belongs to (system, toolchain, library revision),
a SHA-256 of the statement text, assumptions, aliases, provenance, dependency edges and,
for theorems proved through PyLeanX, the verification evidence.

Trust rules
-----------
* An entry is a *pointer*, not a proof. Using it puts the name into Lean source, and the
  kernel checks the use as always; ``verified`` still requires the batch audit.
* :meth:`TheoremBank.ref` and :meth:`TheoremBank.load` refuse entries whose formalization
  differs from the current project (toolchain or library revision): a name may mean
  something else, or nothing, in another version.
* Entries from other systems (``system != "lean4"``) and cross-system ``related`` links are
  informational only. Equivalence between formalizations is never assumed; ``ref`` and
  ``load`` raise :class:`CrossSystemError` for them.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import tempfile
import time
from collections.abc import Iterable, Mapping
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

from .errors import PyLeanXError
from .names import validate_qualified_name
from .proofs import Name

if TYPE_CHECKING:
    from .backend.interface import VerificationResult
    from .project import LeanProject
    from .theorem import Theorem

BANK_SCHEMA = 1
_ID_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z0-9_]+)*\Z")


class BankError(PyLeanXError):
    """Theorem-bank lookup or consistency failure."""


class VersionMismatchError(BankError):
    """The entry belongs to a different toolchain or library revision."""


class CrossSystemError(BankError):
    """The entry is not a Lean declaration of this project's formalization."""


def statement_hash(statement: str) -> str:
    return hashlib.sha256(statement.strip().encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class Formalization:
    """Where a statement lives: proof system, toolchain and library at exact revisions."""

    system: str = "lean4"
    library: str = "mathlib"  # "mathlib" (a library declaration) | "pyleanx" (proved here)
    toolchain: str = ""
    library_revision: str = ""

    @classmethod
    def of_project(cls, project: LeanProject, library: str = "mathlib") -> Formalization:
        return cls("lean4", library, project.toolchain or "", project.mathlib_revision or "")

    def compatible_with(self, project: LeanProject) -> bool:
        return (self.system == "lean4" and self.toolchain == (project.toolchain or "")
                and self.library_revision == (project.mathlib_revision or ""))

    def describe(self) -> str:
        return f"{self.system}/{self.library} {self.toolchain} @ {self.library_revision[:12]}"


@dataclass
class BankEntry:
    id: str
    lean_name: str
    kind: str  # "declaration" | "theorem"
    statement: str
    statement_sha256: str
    formalization: Formalization
    imports: tuple[str, ...] = ()
    assumptions: tuple[str, ...] = ()
    aliases: tuple[str, ...] = ()
    tags: tuple[str, ...] = ()
    description: str = ""
    provenance: dict[str, Any] = field(default_factory=dict)
    dependencies: tuple[str, ...] = ()  # bank IDs
    evidence: dict[str, Any] | None = None
    theorem: dict[str, Any] | None = None  # canonical PyLeanX theorem (kind == "theorem")
    related: tuple[dict[str, str], ...] = ()  # informational cross-system links

    def __post_init__(self) -> None:
        if not _ID_RE.match(self.id):
            raise BankError(f"invalid bank id {self.id!r} (dotted identifier segments)")
        if self.formalization.system == "lean4":
            validate_qualified_name(self.lean_name, "Lean declaration name")
            for m in self.imports:
                validate_qualified_name(m, "import module")
        if self.kind not in ("declaration", "theorem"):
            raise BankError(f"unknown entry kind {self.kind!r}")
        if self.kind == "theorem" and self.theorem is None:
            raise BankError("theorem entries must carry their canonical theorem")
        if statement_hash(self.statement) != self.statement_sha256:
            raise BankError(f"{self.id}: statement hash does not match the statement")

    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d["formalization"] = asdict(self.formalization)
        return d

    @classmethod
    def from_dict(cls, d: Mapping[str, Any]) -> BankEntry:
        d = dict(d)
        d["formalization"] = Formalization(**d["formalization"])
        for k in ("imports", "assumptions", "aliases", "tags", "dependencies"):
            d[k] = tuple(d.get(k, ()))
        d["related"] = tuple(dict(r) for r in d.get("related", ()))
        return cls(**d)

    def summary(self) -> str:
        return (f"{self.id}  [{self.lean_name}]  {self.kind}, {self.formalization.describe()}\n"
                f"    {self.statement.splitlines()[0][:110]}")


@dataclass(frozen=True)
class SearchHit:
    entry: BankEntry
    score: float


def _tokens(text: str) -> list[str]:
    out = []
    for word in re.findall(r"[A-Za-z0-9]+", text):
        out.append(word.lower())
    return out


def default_bank_path() -> Path:
    env = os.environ.get("PYLEANX_BANK")
    return Path(env) if env else Path.home() / ".pyleanx" / "bank.json"


# Human-facing metadata for catalog entries: id -> (description, aliases, tags).
CATALOG_META: dict[str, tuple[str, tuple[str, ...], tuple[str, ...]]] = {
    "algebra.sq_nonneg": ("a square is nonnegative", ("square nonnegative",), ("inequality",)),
    "algebra.add_sq": ("binomial formula (a+b)^2", ("binomial square", "square of a sum"),
                       ("identity",)),
    "algebra.sub_sq": ("binomial formula (a-b)^2", ("square of a difference",), ("identity",)),
    "algebra.sq_sub_sq": ("difference of squares", ("difference of squares",), ("identity",)),
    "algebra.two_mul_le_add_sq": ("2ab <= a^2 + b^2", ("am-gm", "am gm two variables"),
                                  ("inequality",)),
    "algebra.abs_add_le": ("|a + b| <= |a| + |b|", ("triangle inequality absolute value",),
                           ("inequality", "abs")),
    "analysis.sin_sq_add_cos_sq": ("sin^2 x + cos^2 x = 1", ("pythagorean identity",),
                                   ("trigonometry",)),
    "analysis.add_one_le_exp": ("x + 1 <= exp x", ("exponential bound",), ("inequality",)),
    "analysis.sq_sqrt": ("sqrt(x)^2 = x for x >= 0", ("square of square root",), ("sqrt",)),
    "geometry.dist_triangle": ("dist x z <= dist x y + dist y z",
                               ("triangle inequality",), ("metric", "geometry")),
    "geometry.angle_add_angle_add_angle_eq_pi": (
        "the angles of a triangle sum to pi", ("triangle angle sum", "angle sum"),
        ("geometry", "triangle")),
    "geometry.pythagoras_iff": (
        "Pythagoras: right angle iff |AC|^2 = |AB|^2 + |BC|^2", ("pythagorean theorem",
                                                                 "pythagoras"),
        ("geometry", "triangle")),
}


class TheoremBank:
    """A local, file-backed index of declarations and PyLeanX-proved theorems."""

    def __init__(self, path: str | os.PathLike[str] | None = None) -> None:
        self.path = Path(path) if path is not None else None
        self._entries: dict[str, BankEntry] = {}
        if self.path is not None and self.path.exists():
            self._load_file(self.path)

    @classmethod
    def open(cls, path: str | os.PathLike[str] | None = None) -> TheoremBank:
        return cls(path if path is not None else default_bank_path())

    # ------------------------------------------------------------------ persistence
    def _load_file(self, path: Path) -> None:
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("schema") != BANK_SCHEMA:
            raise BankError(f"{path}: unsupported bank schema {data.get('schema')!r}")
        for d in data.get("entries", []):
            e = BankEntry.from_dict(d)
            self._entries[e.id] = e

    def to_dict(self) -> dict[str, Any]:
        return {"schema": BANK_SCHEMA,
                "entries": [self._entries[k].to_dict() for k in sorted(self._entries)]}

    def save(self, path: str | os.PathLike[str] | None = None) -> Path:
        target = Path(path) if path is not None else self.path
        if target is None:
            raise BankError("in-memory bank: pass a path to save()")
        target.parent.mkdir(parents=True, exist_ok=True)
        text = json.dumps(self.to_dict(), indent=1, ensure_ascii=False, sort_keys=True)
        fd, tmp = tempfile.mkstemp(prefix=".bank-", suffix=".json", dir=target.parent)
        try:
            with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as fh:
                fh.write(text + "\n")
            os.replace(tmp, target)
        finally:
            if os.path.exists(tmp):
                os.unlink(tmp)
        self.path = target
        return target

    # ------------------------------------------------------------------ basic access
    def __len__(self) -> int:
        return len(self._entries)

    def __iter__(self):
        return iter(sorted(self._entries.values(), key=lambda e: e.id))

    def __contains__(self, key: str) -> bool:
        try:
            self.get(key)
        except BankError:
            return False
        return True

    def get(self, key: str) -> BankEntry:
        """Look up by canonical ID, then by alias (exact, case-insensitive)."""
        if key in self._entries:
            return self._entries[key]
        low = key.lower()
        matches = [e for e in self._entries.values() if low in (a.lower() for a in e.aliases)]
        if len(matches) == 1:
            return matches[0]
        if len(matches) > 1:
            raise BankError(f"alias {key!r} is ambiguous: {[e.id for e in matches]}")
        raise BankError(f"no bank entry {key!r}")

    def add(self, entry: BankEntry, *, replace: bool = False) -> BankEntry:
        if entry.id in self._entries and not replace:
            raise BankError(f"bank already has {entry.id!r} (pass replace=True)")
        for dep in entry.dependencies:
            if dep not in self._entries:
                raise BankError(f"{entry.id}: unknown dependency {dep!r}")
        self._entries[entry.id] = entry
        return entry

    # ------------------------------------------------------------------ adding entries
    def add_declaration(
        self,
        id: str,  # noqa: A002 - the canonical theorem ID
        ref: Name | str,
        statement: str,
        formalization: Formalization,
        *,
        imports: Iterable[str] = (),
        aliases: Iterable[str] = (),
        tags: Iterable[str] = (),
        description: str = "",
        provenance: Mapping[str, Any] | None = None,
        replace: bool = False,
    ) -> BankEntry:
        """Register a library declaration. ``statement`` should come from Lean (see
        :meth:`index_declarations`), never be typed by hand."""
        name = ref.name if isinstance(ref, Name) else ref
        imps = tuple(imports) or (ref.imports if isinstance(ref, Name) else ())
        entry = BankEntry(
            id=id, lean_name=name, kind="declaration", statement=statement,
            statement_sha256=statement_hash(statement), formalization=formalization,
            imports=imps, assumptions=_premises(statement), aliases=tuple(aliases),
            tags=tuple(tags), description=description, provenance=dict(provenance or {}))
        return self.add(entry, replace=replace)

    def index_declarations(
        self,
        items: Mapping[str, Name],
        project: LeanProject | str | None = None,
        *,
        provenance: Mapping[str, Any] | None = None,
        meta: Mapping[str, tuple[str, tuple[str, ...], tuple[str, ...]]] | None = None,
        replace: bool = True,
        timeout: float | None = None,
    ) -> list[BankEntry]:
        """Ask the pinned Lean for each declaration's type and add one entry per item.

        ``items`` maps bank ID -> :class:`Name` (with the imports the name needs).
        Names Lean does not know raise :class:`BankError` (nothing is added).
        """
        from .backend.declarations import check_declarations
        from .project import find_project

        proj = find_project(project)
        imports = {m for ref in items.values() for m in ref.imports}
        infos = check_declarations([r.name for r in items.values()], imports, proj,
                                   timeout=timeout)
        missing = {i: r.name for i, r in items.items() if not infos[r.name].exists}
        if missing:
            raise BankError(f"Lean does not know these declarations: {missing}")
        form = Formalization.of_project(proj, "mathlib")
        meta = meta or {}
        out = []
        for bid, ref in items.items():
            desc, aliases, tags = meta.get(bid, ("", (), ()))
            out.append(self.add_declaration(
                bid, ref, infos[ref.name].type or "", form, aliases=aliases, tags=tags,
                description=desc, provenance=dict(provenance or {}), replace=replace))
        return out

    def index_catalogs(self, project: LeanProject | str | None = None, *,
                       timeout: float | None = None) -> list[BankEntry]:
        """Index the curated domain catalogs (``pyleanx.algebra`` …) with Lean's types."""
        from ._domain import CATALOG_VERSION, all_catalogs

        items: dict[str, Name] = {}
        for module, cat in all_catalogs().items():
            for key, ref in cat.items():
                items[f"{module}.{key}"] = ref
        prov = {"source": "pyleanx domain catalogs", "catalog_version": CATALOG_VERSION}
        return self.index_declarations(items, project, provenance=prov, meta=CATALOG_META,
                                       timeout=timeout)

    def add_theorem(
        self,
        theorem: Theorem,
        result: VerificationResult,
        *,
        id: str,  # noqa: A002
        aliases: Iterable[str] = (),
        tags: Iterable[str] = (),
        description: str = "",
        dependencies: Iterable[str] = (),
        provenance: Mapping[str, Any] | None = None,
        replace: bool = False,
    ) -> BankEntry:
        """Store a theorem proved through PyLeanX together with its verification evidence.

        Only ``verified`` results are accepted, and the result must be for this exact
        statement (its Lean source contains the rendered statement).
        """
        from .imports import resolve_imports
        from .render.lean import render_statement

        if not result.verified:
            raise BankError(f"{theorem.name}: only verified theorems can be banked "
                            f"(status {result.status})")
        if result.theorem != theorem.name:
            raise BankError(f"result is for {result.theorem!r}, not {theorem.name!r}")
        statement = render_statement(theorem)
        if statement not in result.lean_source and \
                render_statement(theorem, unicode_types=True) not in result.lean_source:
            raise BankError(f"{theorem.name}: the verification result is for a different "
                            "statement")
        from .proofs import cited_theorems

        deps = tuple(dependencies)
        for cited in cited_theorems([theorem]):  # theorems its proof cites, if banked
            for e in self._entries.values():
                if e.kind == "theorem" and e.lean_name == cited.name and e.id not in deps:
                    deps = (*deps, e.id)
        imports = resolve_imports([theorem])
        for d in deps:
            dep = self.get(d)
            imports = tuple(sorted(set(imports) | set(dep.imports)))
        form = Formalization("lean4", "pyleanx", result.toolchain or "",
                             result.mathlib_revision or "")
        evidence = {
            "status": str(result.status), "fingerprint": result.fingerprint,
            "axioms": list(result.axioms or ()), "toolchain": result.toolchain,
            "mathlib_revision": result.mathlib_revision, "policy": result.policy,
            "backend": result.backend, "raw_tactics_used": result.raw_tactics_used,
            "recorded_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        }
        entry = BankEntry(
            id=id, lean_name=theorem.name, kind="theorem", statement=statement,
            statement_sha256=statement_hash(statement), formalization=form, imports=imports,
            assumptions=tuple(f"{h.name} : {h.prop.to_lean()}" for h in theorem.assumptions),
            aliases=tuple(aliases), tags=tuple(tags),
            description=description or (theorem.__doc__ or "").strip(),
            provenance=dict(provenance or {"source": "pyleanx"}), dependencies=deps,
            evidence=evidence, theorem=theorem.canonical())
        return self.add(entry, replace=replace)

    def link(self, id: str, system: str, external_id: str, note: str = "") -> BankEntry:  # noqa: A002
        """Record an *informational* link to a statement in another system/library.

        Links are never used for proofs; no equivalence is assumed or checked.
        """
        e = self.get(id)
        e.related = (*e.related, {"system": system, "id": external_id, "note": note,
                                  "status": "unverified"})
        return e

    # ------------------------------------------------------------------ search
    def search(self, query: str, limit: int = 10, *, kind: str | None = None,
               tags: Iterable[str] = ()) -> list[SearchHit]:
        """Keyword search over IDs, Lean names, aliases, tags, descriptions, statements."""
        q = query.strip().lower()
        qtok = _tokens(q)
        want_tags = {t.lower() for t in tags}
        hits = []
        for e in self._entries.values():
            if kind and e.kind != kind:
                continue
            if want_tags and not want_tags <= {t.lower() for t in e.tags}:
                continue
            score = 0.0
            aliases = [a.lower() for a in e.aliases]
            if q in (e.id.lower(), e.lean_name.lower()) or q in aliases:
                score += 10
            if any(q and q in a for a in aliases) or (q and q in e.description.lower()):
                score += 4
            fields = [
                (3.0, _tokens(e.id) + _tokens(e.lean_name.replace("_", " "))),
                (2.0, [t for a in aliases for t in _tokens(a)] + [t.lower() for t in e.tags]),
                (1.0, _tokens(e.description)),
                (0.5, _tokens(e.statement)),
            ]
            for tok in qtok:
                for weight, toks in fields:
                    if tok in toks:
                        score += weight
            if score > 0:
                hits.append(SearchHit(e, score))
        hits.sort(key=lambda h: (-h.score, h.entry.id))
        return hits[:limit]

    # ------------------------------------------------------------------ using entries
    def _check_usable(self, e: BankEntry, project: LeanProject) -> None:
        f = e.formalization
        if f.system != "lean4":
            raise CrossSystemError(
                f"{e.id} is a {f.system} statement; PyLeanX never assumes it is equivalent "
                "to any Lean declaration")
        if not f.compatible_with(project):
            raise VersionMismatchError(
                f"{e.id} was recorded for {f.describe()}, but the project uses "
                f"{project.toolchain} @ {str(project.mathlib_revision)[:12]}; re-index it "
                "for this version")

    def ref(self, key: str, project: LeanProject | str | None = None) -> Name:
        """A lemma reference (with imports) for a *library declaration* entry."""
        from .project import find_project

        e = self.get(key)
        self._check_usable(e, find_project(project))
        if e.kind != "declaration":
            raise BankError(f"{e.id} is a PyLeanX theorem; use bank.load({e.id!r}) (or "
                            "bank.load_with_dependencies) and verify it in the same batch")
        return Name(e.lean_name, e.imports)

    def load(self, key: str, project: LeanProject | str | None = None) -> Theorem:
        """Rebuild a banked PyLeanX theorem (statement + proof) exactly as recorded."""
        from .project import find_project
        from .render.lean import render_statement
        from .serialize import theorem_from_canonical

        e = self.get(key)
        self._check_usable(e, find_project(project))
        if e.kind != "theorem" or e.theorem is None:
            raise BankError(f"{e.id} is a library declaration; use bank.ref({e.id!r})")
        # Lemma references in the canonical proof do not record their modules; the entry
        # stores the resolved import list of the verified module.
        thm = theorem_from_canonical(e.theorem, imports=e.imports)
        if statement_hash(render_statement(thm)) != e.statement_sha256:
            raise BankError(f"{e.id}: rebuilt statement does not match the recorded hash")
        from .proofs import CITED_THEOREMS

        CITED_THEOREMS[thm.name] = thm  # later loads may cite it
        return thm

    def load_with_dependencies(self, key: str,
                               project: LeanProject | str | None = None) -> list[Theorem]:
        """The theorem and the banked theorems it depends on, dependencies first."""
        order: list[str] = []

        def visit(k: str, stack: tuple[str, ...]) -> None:
            e = self.get(k)
            if e.id in stack:
                raise BankError(f"dependency cycle through {e.id}")
            for d in e.dependencies:
                visit(d, (*stack, e.id))
            if e.id not in order:
                order.append(e.id)

        visit(key, ())
        return [self.load(k, project) for k in order if self.get(k).kind == "theorem"]


def _premises(statement: str) -> tuple[str, ...]:
    """Rough split of a ``#check`` type into binder groups/premises (display/search only)."""
    parts = [p.strip() for p in re.split(r"\s→\s|,\s(?=\S)", statement) if p.strip()]
    return tuple(parts[:-1]) if len(parts) > 1 else ()


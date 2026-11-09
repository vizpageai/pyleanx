"""Python bindings generated from Lean: use any Mathlib or library declaration by name.

    from pyleanx import lib
    RVM = lib.use("ComparatorChallenges.VlasovMaxwell").OAI.RVM
    v = pl.var("v", RVM.Vec)             # a Lean type is a sort
    RVM.q(v)                             # a Lean definition is a function
    RVM.Admissible(d)                    # a predicate gives a proposition
    pl.exact(RVM.one_le_q(v))            # a theorem is a citable lemma

Declarations are exported by running a small Lean metaprogram (in the pinned toolchain)
over the requested modules; the result is cached per module set and pin configuration.
Python learns names, kinds, explicit arity and result types for display and light sort
bookkeeping; *Lean* still elaborates and checks every use.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import uuid
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .errors import ProjectError, PyLeanXError
from .names import validate_qualified_name
from .proofs import Name
from .terms import Const
from .types import NUMERIC_SORTS, UNKNOWN, Prop, Sort, lean_type

__all__ = ["Decl", "Namespace", "use", "get", "export_declarations", "write_bindings"]

EXPORTER_VERSION = "1"

_EXPORTER = r"""import Lean
{imports}

open Lean Meta

private def pyleanxBinder : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict"
  | .instImplicit => "instance"

private def pyleanxKind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

private def pyleanxPP (e : Expr) : MetaM String := do
  return toString (← ppExpr e)

#eval show MetaM Unit from do
  let env ← getEnv
  let targets : Array Name := #[{targets}]
  let mut out : Array Json := #[]
  for (modName, data) in env.header.moduleNames.zip env.header.moduleData do
    if !targets.contains modName then continue
    for n in data.constNames do
      if n.isInternal then continue
      let some ci := env.find? n | continue
      try
        let info ← forallTelescope ci.type fun xs body => do
          let mut bs : Array Json := #[]
          for x in xs do
            let d ← x.fvarId!.getDecl
            bs := bs.push (Json.mkObj [("name", toJson d.userName.toString),
              ("kind", toJson (pyleanxBinder d.binderInfo)), ("type", toJson (← pyleanxPP d.type))])
          return (bs, ← pyleanxPP body, body.isProp, body.isSort && !body.isProp)
        let (binders, result, resultIsProp, resultIsType) := info
        let isProof ← isProp ci.type
        let fields : Array String :=
          if isStructure env n then (getStructureFields env n).map (·.toString) else #[]
        let doc ← findDocString? env n
        out := out.push (Json.mkObj [
          ("name", toJson n.toString), ("module", toJson modName.toString),
          ("kind", toJson (pyleanxKind ci)), ("type", toJson (← pyleanxPP ci.type)),
          ("binders", Json.arr binders), ("result", toJson result),
          ("result_is_prop", toJson resultIsProp), ("result_is_type", toJson resultIsType),
          ("is_proof", toJson isProof), ("fields", toJson fields), ("doc", toJson doc)])
      catch _ => pure ()
  IO.FS.writeFile "{out_path}" (Json.compress (Json.arr out))
"""

_SKIP_LAST = re.compile(r"^(_|match_\d|proof_\d|eq_\d|eq_def$|sizeOf_spec$|injEq$|inj$|"
                        r"noConfusion|noConfusionType$|recOn$|casesOn$|rec$|below$|brecOn$|"
                        r"binductionOn$|ibelow$|ctorIdx|instDecidableEq|instRepr|instInhabited)")


@dataclass(frozen=True)
class Decl:
    """A Lean declaration as reported by Lean."""

    name: str
    module: str
    kind: str
    type: str
    binders: tuple[tuple[str, str, str], ...]  # (name, kind, type)
    result: str
    result_is_prop: bool
    result_is_type: bool
    is_proof: bool
    fields: tuple[str, ...] = ()
    doc: str | None = None

    @property
    def explicit(self) -> tuple[tuple[str, str, str], ...]:
        return tuple(b for b in self.binders if b[1] == "explicit")

    def signature(self) -> str:
        return f"{self.name} : {self.type}"


def _cache_dir(project: Any) -> Path:
    return Path(project.path) / ".pyleanx" / "bindings"


def export_declarations(modules: Sequence[str], project: Any = None, *,
                        timeout: float | None = None, refresh: bool = False) -> list[Decl]:
    """All public declarations of ``modules`` (one Lean run; cached)."""
    from .project import find_project

    proj = find_project(project)
    proj.validate()
    mods = sorted({validate_qualified_name(m, "module") for m in modules})
    if not mods:
        raise PyLeanXError("export_declarations needs at least one module")
    key = hashlib.sha256(json.dumps([EXPORTER_VERSION, mods, proj.config_hash(),
                                     proj.libraries_hash()]).encode()).hexdigest()[:24]
    cache = _cache_dir(proj) / f"{key}.json"
    if cache.exists() and not refresh:
        raw = json.loads(cache.read_text(encoding="utf-8"))
    else:
        raw = _run_exporter(proj, mods, timeout)
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_text(json.dumps(raw, ensure_ascii=False), encoding="utf-8")
    out = []
    for d in raw:
        last = d["name"].rsplit(".", 1)[-1]
        if _SKIP_LAST.match(last) or "._" in d["name"] or d["kind"] in ("recursor", "quot"):
            continue
        out.append(Decl(d["name"], d["module"], d["kind"], d["type"],
                        tuple((b["name"], b["kind"], b["type"]) for b in d["binders"]),
                        d["result"], d["result_is_prop"], d["result_is_type"], d["is_proof"],
                        tuple(d.get("fields") or ()), d.get("doc")))
    return out


def _run_exporter(proj: Any, mods: list[str], timeout: float | None) -> list[dict]:
    work = Path(proj.path) / ".pyleanx" / "build" / uuid.uuid4().hex
    work.mkdir(parents=True, exist_ok=True)
    out_path = (work / "decls.json").resolve()
    src = _EXPORTER.format(imports="\n".join(f"import {m}" for m in mods),
                           targets=", ".join(f"`{m}" for m in mods),
                           out_path=out_path.as_posix())
    lean_file = work / "PyLeanXExport.lean"
    lean_file.write_text(src, encoding="utf-8", newline="\n")
    env = proj.lake_env()
    run_env = {**os.environ, **env}
    try:
        res = subprocess.run([env["LEAN"], str(lean_file)], cwd=proj.path, env=run_env,
                             capture_output=True, text=True, encoding="utf-8", errors="replace",
                             timeout=timeout or max(proj.timeout, 1800), check=False)
        if res.returncode != 0 or not out_path.exists():
            raise ProjectError("declaration export failed:\n"
                               + (res.stdout + res.stderr).strip()[-3000:])
        return json.loads(out_path.read_text(encoding="utf-8"))
    except subprocess.TimeoutExpired as exc:
        raise ProjectError("declaration export timed out") from exc
    finally:
        shutil.rmtree(work, ignore_errors=True)


# =====================================================================================
# Decl -> Python objects
# =====================================================================================

_PRIMITIVE = {"ℝ": "Real", "Real": "Real", "ℕ": "Nat", "Nat": "Nat", "ℤ": "Int", "Int": "Int",
              "ℚ": "Rat", "Rat": "Rat"}


def sort_from_text(text: str, imports: tuple[str, ...], bound: Iterable[str] = ()) -> Sort:
    """A PyLeanX sort for Lean type text (open :class:`LeanType` unless primitive)."""
    t = text.strip()
    if t == "Prop":
        return Prop
    prim = _PRIMITIVE.get(t)
    if prim is not None:
        return next(s for s in NUMERIC_SORTS if s.name == prim)
    words = set(re.findall(r"[^\s()\[\]{},:→×]+", t))
    if words & set(bound):  # depends on earlier arguments: Lean must work it out
        return UNKNOWN
    try:
        return lean_type(t, imports)
    except PyLeanXError:
        return UNKNOWN


_SUB = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")


def ascii_alias(name: str) -> str:
    """Python-identifier spelling of a Lean name component (``f₀`` -> ``f0``)."""
    out = name.translate(_SUB).replace("'", "_prime").replace("!", "_bang").replace("?", "_q")
    return out if out.isidentifier() else re.sub(r"\W", "_", out)


class Namespace:
    """Attribute access to declarations: ``ns.OAI.RVM.q``."""

    def __init__(self, path: str, registry: dict[str, Any], children: dict[str, Namespace]):
        object.__setattr__(self, "_path", path)
        object.__setattr__(self, "_registry", registry)
        object.__setattr__(self, "_children", children)

    def __getattr__(self, attr: str) -> Any:
        if attr.startswith("__"):
            raise AttributeError(attr)
        children: dict[str, Namespace] = self._children
        real = attr if attr in children else _alias_lookup(children, attr)
        if real is None:
            raise AttributeError(f"no declaration or namespace {self._join(attr)!r}; "
                                 f"available: {sorted(children)[:20]}")
        full = self._join(real)
        if full in self._registry:
            return self._registry[full]
        return children[real]

    def _join(self, attr: str) -> str:
        return f"{self._path}.{attr}" if self._path else attr

    def __dir__(self) -> list[str]:
        return sorted({ascii_alias(c) for c in self._children})

    def __getitem__(self, name: str) -> Any:
        return get(self._join(name))

    def __repr__(self) -> str:
        return f"<pyleanx namespace {self._path or '(root)'}: {len(self._children)} entries>"


def _alias_lookup(children: dict[str, Namespace], attr: str) -> str | None:
    for k in children:
        if ascii_alias(k) == attr:
            return k
    return None


_REGISTRY: dict[str, Any] = {}
_DECLS: dict[str, Decl] = {}
_ROOT_CHILDREN: dict[str, Any] = {}


def _node(path_parts: list[str]) -> dict[str, Any]:
    cur = _ROOT_CHILDREN
    acc = []
    for part in path_parts:
        acc.append(part)
        nxt = cur.get(part)
        if nxt is None:
            nxt = Namespace(".".join(acc), _REGISTRY, {})
            cur[part] = nxt
        cur = nxt._children
    return cur


def _make_object(d: Decl) -> Any:
    imports = (d.module,)
    if d.is_proof:
        return Name(d.name, imports)
    bound = [b[0] for b in d.binders]
    if d.result_is_type and not d.explicit:
        fields: tuple[tuple[str, Sort], ...] = ()
        if d.fields:
            fl = []
            for f in d.fields:
                proj = _DECLS.get(f"{d.name}.{f}")
                fsort = (sort_from_text(proj.result, imports, [b[0] for b in proj.binders])
                         if proj is not None else UNKNOWN)
                fl.append((f, fsort))
            fields = tuple(fl)
        return lean_type(d.name, imports, fields=fields)
    result = Prop if d.result_is_prop else sort_from_text(d.result, imports, bound)
    arity = len(d.explicit)
    if arity == 0:
        return Const(d.name, result, imports)
    return Const(d.name, UNKNOWN, imports, arity=arity, result=result)


def _register(decls: Iterable[Decl]) -> None:
    decls = list(decls)
    for d in decls:
        _DECLS[d.name] = d
    for d in decls:
        try:
            obj = _make_object(d)
        except PyLeanXError:
            continue
        _REGISTRY[d.name] = obj
        parts = d.name.split(".")
        parent = _node(parts[:-1])
        if parts[-1] not in parent:
            parent[parts[-1]] = Namespace(d.name, _REGISTRY, {})


def use(*modules: str, project: Any = None, timeout: float | None = None) -> Namespace:
    """Load the declarations of ``modules`` and return the root namespace."""
    _register(export_declarations(modules, project, timeout=timeout))
    return Namespace("", _REGISTRY, _ROOT_CHILDREN)


def get(name: str) -> Any:
    """The Python object for a loaded declaration (``get("OAI.RVM.q")``)."""
    if name not in _REGISTRY:
        raise KeyError(f"{name} is not loaded; call pyleanx.lib.use(<its module>) first")
    return _REGISTRY[name]


def decl(name: str) -> Decl:
    """Lean's description (type, binders, docstring) of a loaded declaration."""
    return _DECLS[name]


def search(text: str, limit: int = 20) -> list[Decl]:
    """Loaded declarations whose name, type or docstring contains all words of ``text``."""
    words = text.lower().split()
    hits = [d for d in _DECLS.values()
            if all(w in (d.name + " " + d.type + " " + (d.doc or "")).lower() for w in words)]
    return sorted(hits, key=lambda d: (len(d.name), d.name))[:limit]


def write_bindings(modules: Sequence[str], path: str | os.PathLike[str], *,
                   project: Any = None, timeout: float | None = None) -> Path:
    """Write a Python module with one attribute per declaration (for IDE completion)."""
    decls = export_declarations(modules, project, timeout=timeout)
    _register(decls)
    tree: dict[str, Any] = {}
    for d in decls:
        if d.name not in _REGISTRY:
            continue
        cur = tree
        parts = d.name.split(".")
        for p in parts[:-1]:
            cur = cur.setdefault(p, {})
            if not isinstance(cur, dict):
                break
        else:
            cur.setdefault(parts[-1], d)
    lines = ['"""Generated by `pyleanx bindings`; do not edit.', "",
             "Modules: " + ", ".join(modules), '"""', "",
             "from pyleanx.bindings import get as _get", "from pyleanx.bindings import use as _use",
             "", f"_use({', '.join(repr(m) for m in modules)})", ""]

    def emit(node: dict[str, Any], indent: str) -> None:
        for key in sorted(node):
            val = node[key]
            ident = ascii_alias(key)
            if isinstance(val, dict):
                lines.append(f"{indent}class {ident}:")
                lines.append(f'{indent}    """Lean namespace."""')
                emit(val, indent + "    ")
            else:
                doc = (val.doc or "").strip().splitlines()
                comment = f"  # {doc[0][:80]}" if doc else ""
                lines.append(f"{indent}{ident} = _get({val.name!r}){comment}")

    emit(tree, "")
    out = Path(path)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return out

"""Proof graphs: how a theorem rests on other results, down to Lean's axioms.

    import pyleanx as pl
    g = pl.proof_graph(pl.analysis.sin_sq_add_cos_sq, depth=2)
    print(g)                 # text tree + foundation summary
    g                        # in Jupyter: a diagram (Mermaid) and the tree
    g.axioms                 # ('Classical.choice', 'Quot.sound', 'propext')

Lean reports every dependency: a small metaprogram (run by the pinned toolchain) walks the
constants that occur in each declaration's statement and in its proof (or, for a
definition, its body). Nothing is parsed from source text and nothing is proved here.

What is drawn: theorems, definitions, types and axioms. Lean's internal helpers
(``foo.proof_1``, ``match_1``, ...) are looked through, so their dependencies count for the
declaration that created them; constructors and recursors are shown as their type.
Type-class instances, classes and structure projections (``HAdd.hAdd``, ``instHAdd``, ...)
are plumbing and are not drawn, but they are part of the full closure: the per-node axiom
sets and the foundation summary are computed by Lean over *everything*.
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import uuid
from collections.abc import Iterable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from .errors import ProjectError, PyLeanXError
from .names import validate_qualified_name
from .proofs import Name

__all__ = ["proof_graph", "ProofGraph", "GraphNode"]

GRAPH_VERSION = "2"

# Lean helpers shared with pyleanx.explain: what counts as a drawn declaration.
LEAN_HELPERS = r"""open Lean Meta

private def pgKind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- Constants in the statement (type) of a declaration. -/
private def pgTypeDeps (ci : ConstantInfo) : Array Name := ci.type.getUsedConstants

/-- Constants in the proof / body (and, for types, the constructors). -/
private def pgBodyDeps : ConstantInfo → Array Name
  | .thmInfo v => v.value.getUsedConstants
  | .defnInfo v => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | .inductInfo v => v.ctors.toArray
  | .ctorInfo v => #[v.induct]
  | _ => #[]

private def pgDigits (s : String) (pre : String) : Bool :=
  s.startsWith pre && (s.toList.drop pre.length).all Char.isDigit && s.length > pre.length

/-- Compiler/elaborator helpers that belong to the declaration that created them. -/
private def pgAux (n : Name) : Bool :=
  n.isInternal || match n with
    | .str _ s => pgDigits s "match_" || pgDigits s "proof_" || pgDigits s "eq_"
        || s == "eq_def"
    | _ => true

private def pgIsInductive (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo _) => true
  | _ => false

private def pgGenerated : List String :=
  ["casesOn", "recOn", "rec", "brecOn", "binductionOn", "below", "ibelow", "noConfusion",
   "noConfusionType", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "sizeOf_spec"]

/-- The type a constructor, recursor or recursion helper (`Nat.below`, `Nat.brecOn.go`)
    belongs to; such constants are drawn as that type. -/
private def pgFoldTarget (env : Environment) (n : Name) (ci : ConstantInfo) : Option Name :=
  match ci with
  | .ctorInfo v => some v.induct
  | .recInfo _ => some n.getPrefix
  | _ => match n with
    | .str p s =>
      if pgGenerated.contains s && pgIsInductive env p then some p
      else match p with
        | .str q s2 => if pgGenerated.contains s2 && pgIsInductive env q then some q else none
        | _ => none
    | _ => none

/-- Lean's base logic (`Eq`, `True`, `rfl`, `congrArg`, `Eq.mpr`, simp's `eq_self`, ...):
    summarised under "foundation" rather than drawn, unless every detail is requested.
    Axioms are always drawn. -/
private def pgBaseModule (m : Name) : Bool :=
  m == `Init.Prelude || m == `Init.Core || m == `Init.SimpLemmas || m == `Init.PropLemmas

/-- "show" (drawn), "aux" (looked through), "fold" (drawn as its type), "prune". -/
private def pgRole (env : Environment) (modOf : Std.HashMap Name Name) (showAll : Bool)
    (n : Name) (ci : ConstantInfo) : MetaM String := do
  if (pgFoldTarget env n ci).isSome then return "fold"
  if pgAux n then return "aux"
  if isClass env n then return "prune"
  if (← isInstance n) then return "prune"
  if (← isProjectionFn n) then return "prune"
  if !showAll then
    match ci with
    | .axiomInfo _ => pure ()
    | _ => if pgBaseModule (modOf.getD n .anonymous) then return "prune"
  return "show"

/-- Drawn declarations reached from `start` through helpers only. -/
private def pgVisible (env : Environment) (modOf : Std.HashMap Name Name) (showAll : Bool)
    (self : Name) (start : Array Name) : MetaM (Array Name) := do
  let mut out : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  let mut stack := start.reverse
  while !stack.isEmpty do
    let m := stack.back!
    stack := stack.pop
    if seen.contains m || m == self then continue
    seen := seen.insert m
    let some cm := env.find? m | continue
    let role ← pgRole env modOf showAll m cm
    if role == "show" then
      out := out.push m
    else if role == "aux" then
      stack := stack ++ (pgTypeDeps cm ++ pgBodyDeps cm).reverse
    else if role == "fold" then
      if let some t := pgFoldTarget env m cm then
        stack := stack.push t
  return out

"""

_GRAPHER = "import Lean\n@@IMPORTS@@\n\n" + LEAN_HELPERS + r"""
#eval show MetaM Unit from do
  let env ← getEnv
  let root : Name := @@ROOT@@.toName
  let maxDepth : Nat := @@DEPTH@@
  let maxNodes : Nat := @@MAXNODES@@
  let showAll : Bool := @@SHOWALL@@
  let outPath : String := @@OUT@@
  let some _ := env.find? root
    | IO.FS.writeFile outPath
        (Json.compress (Json.mkObj [("error", toJson s!"unknown constant {root}")]))
  let mut modOf : Std.HashMap Name Name := {}
  for (m, d) in env.header.moduleNames.zip env.header.moduleData do
    for c in d.constNames do
      modOf := modOf.insert c m
  let modName (n : Name) : String := match modOf.get? n with
    | some m => m.toString
    | none => ""
  -- 1. the full closure (everything Lean's kernel needs for `root`)
  let mut depthOf : Std.HashMap Name Nat := {}
  depthOf := depthOf.insert root 0
  let mut queue : Array Name := #[root]
  let mut i := 0
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    let some ci := env.find? n | continue
    let d := depthOf.getD n 0
    for m in pgTypeDeps ci ++ pgBodyDeps ci do
      unless depthOf.contains m do
        depthOf := depthOf.insert m (d + 1)
        queue := queue.push m
  let mut layers : Std.HashMap String Nat := {}
  let mut kinds : Std.HashMap String Nat := {}
  let mut axioms : Array Json := #[]
  let mut primitives : Array Json := #[]
  let mut height : Nat := 0
  let mut named : Nat := 0
  for n in queue do
    let some ci := env.find? n | continue
    let d := depthOf.getD n 0
    if d > height then height := d
    let mn := modName n
    if pgKind ci == "axiom" then
      axioms := axioms.push (Json.mkObj [("name", toJson n.toString), ("module", toJson mn),
        ("type", toJson (toString (← ppExpr ci.type))), ("depth", toJson d)])
    if pgAux n then continue
    named := named + 1
    let layer := match mn.splitOn "." with
      | l :: _ => if l == "" then "?" else l
      | [] => "?"
    layers := layers.insert layer (layers.getD layer 0 + 1)
    kinds := kinds.insert (pgKind ci) (kinds.getD (pgKind ci) 0 + 1)
    if (pgKind ci == "inductive" || n == `Quot) && pgBaseModule (modOf.getD n .anonymous)
        && !isClass env n && !(`Lean).isPrefixOf n && (pgFoldTarget env n ci).isNone then
      primitives := primitives.push
        (Json.mkObj [("name", toJson n.toString), ("module", toJson mn)])
  -- 2. the drawn graph, breadth first from `root`
  let mut shown : Array Name := #[root]
  let mut vdepth : Std.HashMap Name Nat := {}
  vdepth := vdepth.insert root 0
  let mut nodes : Array Json := #[]
  let mut j := 0
  while j < shown.size do
    let n := shown[j]!
    j := j + 1
    let some ci := env.find? n | continue
    let d := vdepth.getD n 0
    let sdeps ← pgVisible env modOf showAll n (pgTypeDeps ci)
    let bdeps ← pgVisible env modOf showAll n (pgBodyDeps ci)
    if d < maxDepth then
      for m in bdeps ++ sdeps do
        if !vdepth.contains m && shown.size < maxNodes then
          vdepth := vdepth.insert m (d + 1)
          shown := shown.push m
    let ty ← try pure (toString (← ppExpr ci.type)) catch _ => pure ""
    let ax ← collectAxioms n
    nodes := nodes.push (Json.mkObj [
      ("name", toJson n.toString), ("kind", toJson (pgKind ci)), ("module", toJson (modName n)),
      ("type", toJson (if ty.length > 600 then String.mk (ty.toList.take 600) ++ " …" else ty)),
      ("depth", toJson d), ("statement_uses", toJson (sdeps.map (·.toString))),
      ("body_uses", toJson (bdeps.map (·.toString))),
      ("axioms", toJson (ax.map (·.toString)))])
  let layerJson := Json.mkObj (layers.toList.map fun (k, v) => (k, toJson v))
  let kindJson := Json.mkObj (kinds.toList.map fun (k, v) => (k, toJson v))
  IO.FS.writeFile outPath (Json.compress (Json.mkObj [
    ("root", toJson root.toString), ("nodes", Json.arr nodes),
    ("closure", Json.mkObj [("constants", toJson queue.size), ("declarations", toJson named),
      ("height", toJson height), ("layers", layerJson), ("kinds", kindJson)]),
    ("axioms", Json.arr axioms), ("primitives", Json.arr primitives)]))
"""


# =====================================================================================
# Result objects
# =====================================================================================

_KIND_ORDER = {"theorem": 0, "def": 1, "opaque": 1, "inductive": 2, "quot": 2, "axiom": 3}

_LAYER_NAMES = {"Mathlib": "Mathlib", "Batteries": "Batteries", "Init": "Lean core",
                "Std": "Lean std", "Lean": "Lean (meta)"}


@dataclass(frozen=True)
class GraphNode:
    """One drawn declaration, as Lean reported it."""

    name: str
    kind: str  # theorem | def | inductive | axiom | opaque | quot
    module: str
    type: str  # the statement, pretty-printed by Lean
    depth: int  # steps from the root in the drawn graph
    statement_uses: tuple[str, ...]  # drawn declarations its statement mentions
    body_uses: tuple[str, ...]  # drawn declarations its proof / definition uses
    axioms: tuple[str, ...]  # every axiom it depends on (full closure, by Lean)

    @property
    def uses(self) -> tuple[str, ...]:
        """Proof/body dependencies first, then statement-only ones."""
        return self.body_uses + tuple(u for u in self.statement_uses if u not in self.body_uses)

    @property
    def layer(self) -> str:
        if self.kind == "axiom":
            return "axiom"
        return _LAYER_NAMES.get(self.module.split(".", 1)[0], self.module.split(".", 1)[0] or "?")


@dataclass(frozen=True)
class ProofGraph:
    """The dependency graph of a declaration, down to the axioms (see module docstring)."""

    root: str
    nodes: dict[str, GraphNode]
    depth: int
    closure: dict[str, Any]  # constants, declarations, height, layers, kinds
    axiom_info: tuple[dict[str, Any], ...]  # name, module, type, depth
    primitives: tuple[str, ...]  # Lean's built-in inductive types the closure reaches
    source: str = field(default="", repr=False)  # the Lean metaprogram that produced it

    # ------------------------------------------------------------------ queries
    @property
    def axioms(self) -> tuple[str, ...]:
        """All axioms the declaration depends on (what ``#print axioms`` reports)."""
        return tuple(sorted(a["name"] for a in self.axiom_info))

    def uses(self, name: str) -> tuple[str, ...]:
        """Drawn dependencies of ``name`` (proof/body first)."""
        return self.nodes[name].uses

    def used_by(self, name: str) -> tuple[str, ...]:
        """Drawn declarations that use ``name`` directly."""
        return tuple(n.name for n in self.nodes.values() if name in n.uses)

    def hidden(self, name: str) -> int:
        """How many of ``name``'s dependencies are beyond the drawn depth / node limit."""
        return sum(1 for u in self.nodes[name].uses if u not in self.nodes)

    def edges(self) -> list[tuple[str, str, str]]:
        """``(user, used, "proof" | "statement")`` between drawn declarations."""
        out = []
        for n in self.nodes.values():
            for u in n.body_uses:
                if u in self.nodes:
                    out.append((n.name, u, "proof"))
            for u in n.statement_uses:
                if u in self.nodes and u not in n.body_uses:
                    out.append((n.name, u, "statement"))
        return out

    # ------------------------------------------------------------------ text
    def tree(self, statements: bool = False, width: int = 100) -> str:
        """The graph as an indented tree; repeated declarations are marked ``↑``."""
        lines: list[str] = []
        printed: set[str] = set()

        def label(n: GraphNode) -> str:
            more = self.hidden(n.name)
            tail = f"  (+{more} more)" if more and n.name not in printed else ""
            return f"{n.name}  [{n.kind} · {n.module or '?'}]{tail}"

        def walk(name: str, prefix: str, last: bool, top: bool) -> None:
            n = self.nodes[name]
            branch = "" if top else ("└─ " if last else "├─ ")
            if name in printed:
                lines.append(f"{prefix}{branch}↑ {name}")
                return
            lines.append(f"{prefix}{branch}{label(n)}")
            printed.add(name)
            child_prefix = prefix + ("" if top else ("   " if last else "│  "))
            if statements and n.type:
                stmt = " ".join(n.type.split())
                if len(stmt) > width:
                    stmt = stmt[: width - 1] + "…"
                lines.append(f"{child_prefix}    : {stmt}")
            kids = sorted((u for u in n.uses if u in self.nodes),
                          key=lambda u: _KIND_ORDER.get(self.nodes[u].kind, 9))
            for k, u in enumerate(kids):
                walk(u, child_prefix, k == len(kids) - 1, False)

        walk(self.root, "", True, True)
        return "\n".join(lines)

    def foundation(self) -> str:
        """Axioms, primitive types and the size of the full closure."""
        c = self.closure
        layers = ", ".join(f"{_LAYER_NAMES.get(k, k)} {v:,}"
                           for k, v in sorted(c.get("layers", {}).items(), key=lambda kv: -kv[1]))
        out = [f"Foundation of {self.root}:",
               f"  axioms: {', '.join(self.axioms) or 'none'}"]
        for a in self.axiom_info:
            out.append(f"    {a['name']} : {' '.join(str(a['type']).split())}")
        if self.primitives:
            prims = ", ".join(self.primitives[:24]) + (" …" if len(self.primitives) > 24 else "")
            out.append(f"  Lean's built-in types reached: {prims}")
        out.append(f"  full closure: {c.get('declarations', 0):,} declarations ({layers}); "
                   f"longest dependency chain: {c.get('height', 0)} steps")
        return "\n".join(out)

    def __str__(self) -> str:
        return self.tree() + "\n\n" + self.foundation()

    # ------------------------------------------------------------------ diagrams
    def _ids(self) -> dict[str, str]:
        return {name: f"n{i}" for i, name in enumerate(self.nodes)}

    def to_mermaid(self) -> str:
        """A Mermaid flowchart (renders in JupyterLab, GitHub and MkDocs)."""
        ids = self._ids()
        lines = ["flowchart TD"]
        for name, n in self.nodes.items():
            text = _mermaid_text(f"{name}\n{n.kind} · {n.layer}")
            shape = ("[(", ")]") if n.kind == "axiom" else (("([", "])") if n.kind in
                                                             ("inductive", "quot") else ("[", "]"))
            lines.append(f'  {ids[name]}{shape[0]}"{text}"{shape[1]}')
        for a, b, how in self.edges():
            lines.append(f"  {ids[a]} {'-->' if how == 'proof' else '-.->'} {ids[b]}")
        # Foundation: every axiom, linked from the drawn frontier that depends on it.
        ax_ids = {}
        for k, a in enumerate(self.axioms):
            if a in self.nodes:
                ax_ids[a] = ids[a]
                continue
            ax_ids[a] = f"ax{k}"
            lines.append(f'  ax{k}[("{_mermaid_text(a + chr(10) + "axiom")}")]')
        for name, n in self.nodes.items():
            if n.kind == "axiom" or not (self.hidden(name) or not n.uses):
                continue
            for a in n.axioms:
                if a not in self.nodes:
                    lines.append(f"  {ids[name]} -.- {ax_ids[a]}")
        classes = {"Mathlib": "mathlib", "Batteries": "batteries", "Lean core": "core",
                   "axiom": "axiom"}
        lines += ["  classDef root stroke-width:3px",
                  "  classDef mathlib fill:#e8f0fe,stroke:#3b6fd8",
                  "  classDef batteries fill:#fdf2e3,stroke:#c98a1b",
                  "  classDef core fill:#e7f6ec,stroke:#2f8f4e",
                  "  classDef axiom fill:#fde8e8,stroke:#c0392b"]
        for name, n in self.nodes.items():
            cls = classes.get(n.layer)
            if cls:
                lines.append(f"  class {ids[name]} {cls}")
        for a, i in ax_ids.items():
            if a not in self.nodes:
                lines.append(f"  class {i} axiom")
        lines.append(f"  class {ids[self.root]} root")
        return "\n".join(lines)

    def to_dot(self) -> str:
        """A Graphviz DOT graph (``dot -Tsvg``)."""
        ids = self._ids()
        colors = {"Mathlib": "#e8f0fe", "Batteries": "#fdf2e3", "Lean core": "#e7f6ec",
                  "axiom": "#fde8e8"}
        out = ["digraph proof {", "  rankdir=TB; node [shape=box, style=filled, fontsize=10];"]
        for name, n in self.nodes.items():
            label = json.dumps(name + "\n" + n.kind + " · " + n.layer, ensure_ascii=False)
            out.append(f'  {ids[name]} [label={label}, '
                       f'fillcolor="{colors.get(n.layer, "#ffffff")}"];')
        for a, b, how in self.edges():
            out.append(f"  {ids[a]} -> {ids[b]}{' [style=dashed]' if how == 'statement' else ''};")
        for k, a in enumerate(self.axioms):
            if a not in self.nodes:
                out.append(f'  ax{k} [label={json.dumps(a + chr(10) + "axiom")}, '
                           f'shape=cylinder, fillcolor="{colors["axiom"]}"];')
        out.append("}")
        return "\n".join(out)

    def to_json(self) -> dict[str, Any]:
        return {"root": self.root, "depth": self.depth,
                "nodes": [n.__dict__ | {"statement_uses": list(n.statement_uses),
                                        "body_uses": list(n.body_uses), "axioms": list(n.axioms)}
                          for n in self.nodes.values()],
                "closure": self.closure, "axioms": list(self.axiom_info),
                "primitives": list(self.primitives)}

    def to_html(self) -> str:
        """A standalone page (diagram via the Mermaid CDN, plus the tree)."""
        import html

        return ("<!doctype html><meta charset='utf-8'><title>" + html.escape(self.root)
                + "</title><body style='font-family:system-ui;margin:16px'>"
                + f"<h2>{html.escape(self.root)}</h2><pre class='mermaid'>"
                + html.escape(self.to_mermaid()) + "</pre><pre>" + html.escape(str(self))
                + "</pre><script type='module'>import mermaid from "
                "'https://cdn.jsdelivr.net/npm/mermaid@10.9.1/dist/mermaid.esm.min.mjs';"
                "mermaid.initialize({startOnLoad:true});</script></body>")

    def save_html(self, path: str | os.PathLike[str]) -> Path:
        p = Path(path)
        p.write_text(self.to_html(), encoding="utf-8")
        return p

    def _repr_markdown_(self) -> str:  # Jupyter (JupyterLab >= 4.1 renders Mermaid)
        return (f"**Proof graph of `{self.root}`** — solid: used in the proof; dotted: "
                f"mentioned in the statement; thin links: axioms.\n\n```mermaid\n"
                f"{self.to_mermaid()}\n```\n\n```text\n{self.foundation()}\n```\n\n"
                f"<details><summary>tree</summary>\n\n```text\n{self.tree(statements=True)}\n"
                "```\n</details>")


def _mermaid_text(s: str) -> str:
    return (s.replace("&", "&amp;").replace('"', "#quot;").replace("<", "&lt;")
            .replace(">", "&gt;").replace("\n", "<br/>"))


# =====================================================================================
# Running Lean
# =====================================================================================

def _target(item: Name | str) -> tuple[str, tuple[str, ...]]:
    if isinstance(item, Name):
        return item.name, item.imports
    if isinstance(item, str):
        name = validate_qualified_name(item, "declaration name")
        from . import mathlib

        found = mathlib.find(name)
        if found is None:
            return name, ()
        mod = found[0]
        return name, (() if mod == "Init" or mod.startswith("Init.") else (mod,))
    raise TypeError(f"expected a declaration name or a lemma reference, got {item!r}")


def from_json(raw: dict[str, Any], depth: int, source: str = "") -> ProofGraph:
    if "error" in raw:
        raise ProjectError(f"Lean: {raw['error']}")
    nodes = {}
    for d in raw["nodes"]:
        nodes[d["name"]] = GraphNode(d["name"], d["kind"], d["module"], d["type"], d["depth"],
                                     tuple(d["statement_uses"]), tuple(d["body_uses"]),
                                     tuple(sorted(d["axioms"])))
    return ProofGraph(raw["root"], nodes, depth, dict(raw["closure"]),
                      tuple(sorted(raw["axioms"], key=lambda a: a["name"])),
                      tuple(p["name"] for p in raw["primitives"]), source)


def proof_graph(
    item: Name | str,
    depth: int = 2,
    *,
    max_nodes: int = 60,
    detail: str = "lemmas",
    imports: Iterable[str] = (),
    project: object = None,
    timeout: float | None = None,
    refresh: bool = False,
) -> ProofGraph:
    """The proof graph of a Lean/Mathlib declaration, down to its axioms.

    ``item`` is a name (``"Real.sin_sq_add_cos_sq"``, module found automatically), a
    catalog lemma (``pl.analysis.sin_sq_add_cos_sq``), ``pl.mathlib.<name>`` or
    ``pl.ref(...)``. ``depth`` limits how many levels are drawn and ``max_nodes`` how many
    declarations; the axioms and closure statistics always cover everything.
    ``detail="lemmas"`` (default) summarises Lean's base logic (``Eq``, ``rfl``,
    ``congrArg``, simp's ``eq_self``, ...) under "foundation" instead of drawing it;
    ``detail="all"`` draws it too. One Lean run, cached per pin configuration.
    """
    if depth < 0 or max_nodes < 1:
        raise PyLeanXError("depth must be >= 0 and max_nodes >= 1")
    if detail not in ("lemmas", "all"):
        raise PyLeanXError("detail must be 'lemmas' or 'all'")
    from .project import find_project

    name, mods = _target(item)
    modules = sorted({validate_qualified_name(m, "module") for m in (*mods, *imports)})
    proj = find_project(project)  # type: ignore[arg-type]
    proj.validate()
    key = hashlib.sha256(json.dumps([GRAPH_VERSION, name, modules, depth, max_nodes, detail,
                                     proj.config_hash(), proj.libraries_hash()]).encode())
    cache = Path(proj.path) / ".pyleanx" / "proofgraph" / f"{key.hexdigest()[:24]}.json"
    if cache.exists() and not refresh:
        return from_json(json.loads(cache.read_text(encoding="utf-8")), depth)
    raw, source = _run(proj, name, modules, depth, max_nodes, detail == "all", timeout)
    graph = from_json(raw, depth, source)
    cache.parent.mkdir(parents=True, exist_ok=True)
    cache.write_text(json.dumps(raw, ensure_ascii=False), encoding="utf-8")
    return graph


def lean_source(name: str, modules: Iterable[str], depth: int, max_nodes: int,
                out_path: str, show_all: bool = False) -> str:
    """The Lean metaprogram for one graph (exposed for inspection and tests)."""
    return (_GRAPHER.replace("@@IMPORTS@@", "\n".join(f"import {m}" for m in modules))
            .replace("@@ROOT@@", json.dumps(name, ensure_ascii=False))
            .replace("@@DEPTH@@", str(int(depth)))
            .replace("@@MAXNODES@@", str(int(max_nodes)))
            .replace("@@SHOWALL@@", "true" if show_all else "false")
            .replace("@@OUT@@", json.dumps(out_path)))


def _run(proj: Any, name: str, modules: list[str], depth: int, max_nodes: int,
         show_all: bool, timeout: float | None) -> tuple[dict[str, Any], str]:
    work = Path(proj.path) / ".pyleanx" / "build" / uuid.uuid4().hex
    work.mkdir(parents=True, exist_ok=True)
    out_path = (work / "graph.json").resolve()
    src = lean_source(name, modules, depth, max_nodes, out_path.as_posix(), show_all)
    lean_file = work / "PyLeanXProofGraph.lean"
    lean_file.write_text(src, encoding="utf-8", newline="\n")
    env = proj.lake_env()
    try:
        res = subprocess.run([env["LEAN"], str(lean_file)], cwd=proj.path,
                             env={**os.environ, **env}, capture_output=True, text=True,
                             encoding="utf-8", errors="replace",
                             timeout=timeout or proj.timeout, check=False)
        if res.returncode != 0 or not out_path.exists():
            raise ProjectError("proof graph failed:\n" + (res.stdout + res.stderr).strip()[-3000:])
        return json.loads(out_path.read_text(encoding="utf-8")), src
    except subprocess.TimeoutExpired as exc:
        raise ProjectError(f"proof graph of {name} timed out; pass a larger timeout=") from exc
    finally:
        shutil.rmtree(work, ignore_errors=True)

"""Index of every Mathlib declaration name -> defining module, from the pinned sources.

Built once per Mathlib revision by scanning ``.lake/packages/mathlib/Mathlib/**.lean``
(no Lean run), cached in ``<project>/.pyleanx/mathlib-index-<rev>.json``. It records
theorems/lemmas, definitions, types (structure/class/inductive) and aliases, tracks
``namespace``/``section``/``end``, and derives the names ``@[to_additive]`` generates.

The index only says *where* a name lives, so PyLeanX can import the right module. Lean
still checks every use; a wrong entry can only make Lean report an unknown identifier.
"""

from __future__ import annotations

import json
import os
import re
from collections.abc import Iterator
from pathlib import Path
from typing import Any

INDEX_VERSION = "4"
#: Module tag for Lean core (`Init`): always available, nothing to import.
CORE = "Init"

_DECL = re.compile(
    r"^(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|alias|"
    r"irreducible_def)\s+"
    r"(?!⟨)([^\s:(\[{⦃]+)")
_PRIVATE = re.compile(r"^(?:[a-z]+\s+)*private\s")
_NS = re.compile(r"^namespace\s+(\S+)")
_SECTION = re.compile(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$")
_END = re.compile(r"^end(?:\s+(\S+))?\s*$")
_ALIAS_PAIR = re.compile(r"^alias\s+⟨([^⟩]*)⟩")
_TO_ADD = re.compile(r"to_additive(?:\s+\([^)]*\))*(?:\s+([A-Za-z_][\w.'₀-₉]*))?")
_KIND = {"theorem": "theorem", "lemma": "theorem", "alias": "theorem", "def": "def",
         "abbrev": "def", "opaque": "def", "axiom": "theorem", "structure": "type",
         "class": "type", "inductive": "type", "irreducible_def": "def"}

# Word-level translation used by @[to_additive] when no explicit name is given.
_ADDITIVE = {"mabs": "abs", "prod": "sum", "mul": "add", "one": "zero", "inv": "neg", "div": "sub",
             "pow": "nsmul", "npow": "nsmul", "zpow": "zsmul", "smul": "vadd",
             "monoid": "addMonoid", "group": "addGroup", "units": "addUnits",
             "Prod": "Sum", "Monoid": "AddMonoid", "Group": "AddGroup", "Mul": "Add",
             "One": "Zero", "Inv": "Neg", "Div": "Sub", "Pow": "SMul", "Units": "AddUnits",
             "CommMonoid": "AddCommMonoid", "CommGroup": "AddCommGroup",
             "Submonoid": "AddSubmonoid", "Subgroup": "AddSubgroup"}


def _additive_name(name: str) -> str:
    parts = []
    for comp in name.split("."):
        words = comp.split("_")
        parts.append("_".join(_ADDITIVE.get(w, w) for w in words))
    return ".".join(parts)


def _strip_comments(text: str) -> str:
    # block comments (including doc comments), possibly nested once
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group().count("\n"), text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def scan_file(text: str) -> Iterator[tuple[str, str]]:
    """(full name, kind) for declarations in one Lean file."""
    stack: list[tuple[str, str]] = []  # (kind "ns"|"sec", name)
    attrs = ""
    for raw in _strip_comments(text).splitlines():
        line = raw.strip()
        if not line:
            continue
        if raw[0] in " \t":  # inside a declaration body / continued attribute
            if attrs and not line.startswith(("theorem", "lemma", "def")):
                attrs += " " + line
            continue
        m = _NS.match(line)
        if m:
            for part in m.group(1).split("."):
                stack.append(("ns", part))
            continue
        m = _SECTION.match(line)
        if m:
            stack.append(("sec", m.group(1) or ""))
            continue
        m = _END.match(line)
        if m:
            name = m.group(1)
            if name and stack and stack[-1][0] == "ns":
                for _ in name.split("."):
                    if stack:
                        stack.pop()
            elif stack:
                stack.pop()
            continue
        if line.startswith("@["):
            attrs = line
            rest = line[line.find("]") + 1:].strip() if "]" in line else ""
            if not rest:
                continue
            line = rest
        decl_line = re.sub(r"^@\[[^\]]*\]\s*", "", line)
        m = _DECL.match(decl_line)
        pair = _ALIAS_PAIR.match(decl_line)
        if not m and not pair:
            attrs = ""
            continue
        keyword, name = (m.group(1), m.group(2)) if m else ("alias", "")
        private = bool(_PRIVATE.match(decl_line))
        ns = ".".join(n for k, n in stack if k == "ns")
        if keyword == "alias":
            names = [n.strip() for n in pair.group(1).split(",")] if pair else [name]
        else:
            names = [name]
        for n in names:
            rooted = n.startswith("_root_.")
            if rooted:
                n = n[len("_root_."):]
            if not n or private or "«" in n or n.startswith("_") or keyword == "instance":
                continue
            full = n if rooted else (f"{ns}.{n}" if ns else n)
            kind = _KIND[keyword]
            yield full, kind
            if "to_additive" in attrs:
                tm = _TO_ADD.search(attrs)
                explicit = tm.group(1) if tm else None
                if explicit and explicit not in ("existing", "self"):
                    add = explicit if "." in explicit or not ns else f"{ns}.{explicit}"
                    add = add[len("_root_."):] if add.startswith("_root_.") else add
                else:
                    add = _additive_name(full)
                if add != full:
                    yield add, kind
        attrs = ""


def mathlib_source(project: Any) -> Path:
    return Path(project.path) / ".lake" / "packages" / "mathlib"


def _roots(project: Any) -> list[tuple[Path, Path, bool]]:
    """(package root, source dir, is_core) in priority order: core, Batteries, Mathlib."""
    out = []
    try:
        sysroot = Path(project._lake_env_base()["LEAN_SYSROOT"]) / "src" / "lean"
        if (sysroot / "Init").is_dir():
            out.append((sysroot, sysroot / "Init", True))
    except Exception:  # noqa: BLE001 - core names are a convenience
        pass
    pkgs = Path(project.path) / ".lake" / "packages"
    if (pkgs / "batteries" / "Batteries").is_dir():
        out.append((pkgs / "batteries", pkgs / "batteries" / "Batteries", False))
    out.append((mathlib_source(project), mathlib_source(project) / "Mathlib", False))
    return out


def build_index(project: Any, progress: Any = None) -> dict[str, Any]:
    """Scan Lean core, Batteries and Mathlib sources; {"names": {name: [module, kind]}}."""
    roots = _roots(project)
    if not roots[-1][1].is_dir():
        from .errors import ProjectError

        raise ProjectError(f"Mathlib sources not found at {roots[-1][1]} (run `pyleanx init`)")
    names: dict[str, list[str]] = {}
    count = 0
    for root, src, core in roots:
        count = _scan_tree(root, src, core, names, count, progress)
    return {"version": INDEX_VERSION, "mathlib": project.mathlib_revision, "files": count,
            "names": names}


def _scan_tree(root: Path, src: Path, core: bool, names: dict[str, list[str]], count: int,
               progress: Any) -> int:
    for dirpath, _, files in os.walk(src):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            path = Path(dirpath) / fn
            module = CORE if core else ".".join(path.relative_to(root).with_suffix("").parts)
            try:
                text = path.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError):
                continue
            for full, kind in scan_file(text):
                # first definition wins; to_additive copies never override real ones
                names.setdefault(full, [module, kind])
            count += 1
            if progress and count % 1000 == 0:
                progress(f"  … {count} files")
    return count


_CACHE: dict[str, dict[str, Any]] = {}


def load_index(project: Any = None, *, refresh: bool = False, progress: Any = None
               ) -> dict[str, Any]:
    """The cached index for the project's pinned Mathlib (built on first use)."""
    from .project import find_project

    proj = find_project(project)
    rev = proj.mathlib_revision or "unknown"
    key = f"{proj.path}|{rev}"
    if key in _CACHE and not refresh:
        return _CACHE[key]
    f = Path(proj.path) / ".pyleanx" / f"mathlib-index-{rev[:12]}.json"
    data = None
    if f.exists() and not refresh:
        try:
            data = json.loads(f.read_text(encoding="utf-8"))
            if data.get("version") != INDEX_VERSION or data.get("mathlib") != rev:
                data = None
        except (OSError, ValueError):
            data = None
    if data is None:
        if progress:
            progress("indexing the pinned Mathlib sources (once per Mathlib revision) …")
        data = build_index(proj, progress)
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
    _CACHE[key] = data
    return data

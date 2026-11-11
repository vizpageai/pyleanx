"""Explain a library proof step by step, exactly as Lean verified it.

    import pyleanx as pl
    e = pl.explain("Complex.sin_sq_add_cos_sq")
    print(e)            # source, exactness evidence, every step with its goals, lemmas used
    e.deeper("Complex.cosh_sq_sub_sinh_sq")    # explain a lemma the proof used

How it works, and why it is the proof that was verified:

1. Lean (pinned toolchain, in the REPL) imports the compiled module and reports where the
   declaration is defined (module, line range) and a structural hash of its proof term:
   the term the kernel checked when the library was built.
2. The declaration's source file (the pinned package checkout or the toolchain's sources)
   is re-elaborated by Lean in full, in its own context. Lean records every tactic of the
   proof with the goals before and after it and the constants it used.
3. The re-elaborated proof term is hashed again. ``exact`` is True only when the source
   re-elaborated without errors *and* gives the same proof term and statement. Otherwise
   the explanation is still shown, marked as not matching, with the reason.

Every goal, step text and lemma statement here comes from Lean or from the exact source
text; nothing is paraphrased. Nothing here proves anything new.
"""

from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
from collections.abc import Iterable
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from .errors import ProjectError, PyLeanXError
from .names import validate_qualified_name
from .proofgraph import LEAN_HELPERS, _target
from .proofs import Name

__all__ = ["explain", "Explanation", "ProofStep", "LemmaInfo"]

EXPLAIN_VERSION = "1"

_PROBE = r"""open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let n : Name := @@ROOT@@.toName
  let some ci := env.find? n
    | IO.println (Json.compress (Json.mkObj [("error", toJson s!"unknown constant {n}")]))
  let mut modName : String := ""
  for (m, d) in env.header.moduleNames.zip env.header.moduleData do
    if d.constNames.contains n then
      modName := m.toString
  let r ← findDeclarationRanges? n
  let rng : Json := match r with
    | some r => Json.mkObj [("line", toJson r.range.pos.line),
        ("column", toJson r.range.pos.column), ("end_line", toJson r.range.endPos.line),
        ("end_column", toJson r.range.endPos.column)]
    | none => Json.null
  let value : String := match ci with
    | .thmInfo v => toString v.value.hash
    | .defnInfo v => toString v.value.hash
    | .opaqueInfo v => toString v.value.hash
    | _ => ""
  let ty ← try pure (toString (← ppExpr ci.type)) catch _ => pure ""
  IO.println (Json.compress (Json.mkObj [("module", toJson modName), ("range", rng),
    ("value_hash", toJson value), ("type_hash", toJson (toString ci.type.hash)),
    ("type", toJson ty), ("kind", toJson (match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other"))]))
"""

_LEMMAS = LEAN_HELPERS + r"""
#eval show MetaM Unit from do
  let env ← getEnv
  let root : Name := @@ROOT@@.toName
  let steps : Array (Array String) := @@STEPS@@
  let mut modOf : Std.HashMap Name Name := {}
  for (m, d) in env.header.moduleNames.zip env.header.moduleData do
    for c in d.constNames do
      modOf := modOf.insert c m
  let some ci := env.find? root | throwError "unknown constant {root}"
  let cited ← pgVisible env modOf false root (pgBodyDeps ci)
  let mut all : Array Name := cited
  let mut stepUses : Array Json := #[]
  for s in steps do
    let v ← pgVisible env modOf false root (s.map (·.toName))
    for x in v do
      unless all.contains x do all := all.push x
    stepUses := stepUses.push (toJson (v.map (·.toString)))
  let mut lemmas : Array Json := #[]
  for x in all do
    let some c := env.find? x | continue
    let ty ← try pure (toString (← ppExpr c.type)) catch _ => pure ""
    lemmas := lemmas.push (Json.mkObj [("name", toJson x.toString), ("kind", toJson (pgKind c)),
      ("module", toJson (modOf.getD x .anonymous).toString), ("type", toJson ty)])
  IO.println (Json.compress (Json.mkObj [("cited", toJson (cited.map (·.toString))),
    ("steps", Json.arr stepUses), ("lemmas", Json.arr lemmas)]))
"""


# =====================================================================================
# Result objects
# =====================================================================================

@dataclass(frozen=True)
class ProofStep:
    """One tactic of the proof, with the goals Lean showed around it."""

    text: str  # the exact source text of the step
    line: int
    column: int
    depth: int  # nesting (a rewrite rule inside `rw [...]` has depth 1)
    goals_before: tuple[str, ...]
    goals_after: tuple[str, ...]
    uses: tuple[str, ...] = ()  # lemmas/definitions this step used (from Lean)

    @property
    def closes(self) -> bool:
        return not self.goals_after


@dataclass(frozen=True)
class LemmaInfo:
    name: str
    kind: str
    module: str
    statement: str  # as Lean prints it


@dataclass(frozen=True)
class Explanation:
    """A library proof as Lean verified it (see the module docstring)."""

    name: str
    module: str
    file: str  # path of the source file, relative to its package / toolchain
    first_line: int
    last_line: int
    statement: str
    source: str  # the declaration's exact source text
    exact: bool
    evidence: dict[str, Any]
    steps: tuple[ProofStep, ...]
    cited: tuple[str, ...]  # lemmas/definitions in the proof term
    lemmas: dict[str, LemmaInfo] = field(default_factory=dict)
    project: Any = field(default=None, repr=False, compare=False)

    # ------------------------------------------------------------------ navigation
    def deeper(self, name: str, **kw: Any) -> Explanation:
        """Explain a lemma this proof used (``e.deeper("Complex.cosh_sq_sub_sinh_sq")``)."""
        return explain(name, project=kw.pop("project", self.project), **kw)

    @property
    def used(self) -> tuple[str, ...]:
        """Every lemma/definition the proof used: the proof term's, then each step's."""
        out = list(self.cited)
        for s in self.steps:
            out += [u for u in s.uses if u not in out]
        return tuple(out)

    # ------------------------------------------------------------------ text
    def exactness(self) -> str:
        ev = self.evidence
        if self.exact:
            return ("exact: re-elaborating this source gives the same proof term (and "
                    f"statement) that Lean verified [hash {ev.get('value_hash')}]")
        return "NOT shown to be exact: " + str(ev.get("reason", "unknown"))

    def __str__(self) -> str:
        ev = self.evidence
        out = [self.name,
               f"  {self.file}:{self.first_line}-{self.last_line} · {ev.get('package', '')} "
               f"{str(ev.get('revision', ''))[:12]}".rstrip(),
               f"  statement (Lean): {' '.join(self.statement.split())}", "",
               "Proof, as written in the source:"]
        for k, line in enumerate(self.source.splitlines()):
            out.append(f"  {self.first_line + k:>5} │ {line}")
        out += ["", self.exactness()]
        if self.steps:
            out += ["", "Steps (goal before → after):"]
            prev_hyps: tuple[str, ...] | None = None
            for k, s in enumerate(self.steps, 1):
                pad = "   " * s.depth
                step_text = _one_line(s.text.rstrip().rstrip(","), 90)
                out.append(f"  {pad}{k}. {step_text}    ({s.line}:{s.column})")
                for g in s.goals_before[:1]:
                    hyps, target = _split_goal(g)
                    if hyps != prev_hyps:
                        out += [f"  {pad}     {h}" for h in hyps]
                        prev_hyps = hyps
                    out.append(f"  {pad}     ⊢ {target}")
                if len(s.goals_before) > 1:
                    out.append(f"  {pad}     (+{len(s.goals_before) - 1} more goals)")
                used = self._theorems(s.uses)
                if used:
                    out.append(f"  {pad}     uses: {', '.join(used)}")
                after = ("no goals" if s.closes else
                         " | ".join("⊢ " + _split_goal(g)[1] for g in s.goals_after))
                out.append(f"  {pad}     → {after}")
        else:
            out += ["", "The proof is a term (no tactic steps); it is built from the lemmas below."]
        if self.cited:
            out += ["", "Lemmas in the proof term: " + (", ".join(self._theorems(self.cited))
                                                         or "none")]
        for title, want in (("Lemmas used, as Lean states them:", True),
                            ("Definitions, types and axioms involved:", False)):
            rows = [f"  {n} : {' '.join(i.statement.split())}" for n in self.used
                    if (i := self.lemmas.get(n)) is not None and (i.kind == "theorem") == want]
            if rows:
                out += ["", title, *rows]
        return "\n".join(out)

    def _theorems(self, names: Iterable[str]) -> tuple[str, ...]:
        return tuple(n for n in names if (i := self.lemmas.get(n)) is None or i.kind == "theorem")

    def _repr_markdown_(self) -> str:  # Jupyter
        mark = "✅ exact" if self.exact else "⚠️ not shown to be exact"
        return (f"**`{self.name}`** — {mark}\n\n```text\n{self}\n```")

    def to_json(self) -> dict[str, Any]:
        d = asdict(self)
        d.pop("project", None)
        return d


def _one_line(text: str, width: int) -> str:
    s = " ".join(text.split())
    return s if len(s) <= width else s[: width - 1] + "…"


def _split_goal(goal: str) -> tuple[tuple[str, ...], str]:
    lines = goal.splitlines()
    for k, line in enumerate(lines):
        if line.startswith("⊢"):
            return tuple(lines[:k]), " ".join(" ".join(lines[k:])[1:].split())
    return (), " ".join(goal.split())


# =====================================================================================
# Source files and provenance
# =====================================================================================

def _manifest_revs(project_path: Path) -> dict[str, str]:
    try:
        data = json.loads((project_path / "lake-manifest.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    return {p.get("name", ""): p.get("rev", "") for p in data.get("packages", [])}


def source_file(proj: Any, module: str) -> tuple[Path, dict[str, Any]]:
    """The source of ``module`` and where it comes from (package, revision, checks)."""
    rel = Path(*module.split(".")).with_suffix(".lean")
    root = Path(proj.path)
    revs = _manifest_revs(root)
    pkgs = root / ".lake" / "packages"
    for pkg in sorted(pkgs.iterdir()) if pkgs.is_dir() else []:
        f = pkg / rel
        if f.is_file():
            info: dict[str, Any] = {"package": pkg.name, "pinned": revs.get(pkg.name, "")}
            info.update(_git_state(pkg, rel.as_posix()))
            return f, info
    if (root / rel).is_file():  # the user's own project
        return root / rel, {"package": "project"}
    sysroot = proj.lake_env().get("LEAN_SYSROOT")
    if sysroot:
        f = Path(sysroot) / "src" / "lean" / rel
        if f.is_file():
            return f, {"package": "lean4 toolchain", "revision": Path(sysroot).name}
    raise ProjectError(f"no source file for module {module} (looked for {rel})")


def _git_state(repo: Path, rel: str) -> dict[str, Any]:
    git = shutil.which("git")
    if git is None or not (repo / ".git").exists():
        return {}
    try:
        head = subprocess.run([git, "rev-parse", "HEAD"], cwd=repo, capture_output=True,
                              text=True, timeout=60, check=False).stdout.strip()
        dirty = subprocess.run([git, "status", "--porcelain", "--", rel], cwd=repo,
                               capture_output=True, text=True, timeout=60,
                               check=False).stdout.strip()
    except (OSError, subprocess.TimeoutExpired):
        return {}
    return {"revision": head, "modified": bool(dirty)}


# =====================================================================================
# Steps from the REPL's info trees
# =====================================================================================

_WRAPPERS = re.compile(r"(tacticSeq|byTactic|tacticSeq1Indented|tacticSeqBracketed|"
                       r"Term\.paren|nullKind|cdot)")


def _pos(p: Any) -> tuple[int, int]:
    return (p.line, p.column)


def _slice(lines: list[str], start: tuple[int, int], end: tuple[int, int]) -> str:
    (l0, c0), (l1, c1) = start, end
    if l0 == l1:
        return lines[l0 - 1][c0:c1]
    parts = [lines[l0 - 1][c0:], *lines[l0:l1 - 1], lines[l1 - 1][:c1]]
    return "\n".join(parts)


def collect_steps(trees: Iterable[Any], tactics: Iterable[Any], lines: list[str],
                  first: tuple[int, int], last: tuple[int, int]) -> list[dict[str, Any]]:
    """Tactic steps inside ``first..last`` (line, column), from LeanInteract objects."""
    uses = {(_pos(t.start_pos), _pos(t.end_pos)): list(t.used_constants) for t in tactics}
    found: dict[tuple[tuple[int, int], tuple[int, int]], dict[str, Any]] = {}
    for tree in trees:
        for sub in tree.dfs_walk():
            nd = sub.node
            if sub.kind != "TacticInfo" or nd is None:
                continue
            rng = nd.stx.range
            if rng.synthetic:
                continue
            a, b = _pos(rng.start), _pos(rng.finish)
            if a < first or b > last or a == b:
                continue
            text = _slice(lines, a, b)
            if text.strip() in ("by", "") or _WRAPPERS.search(nd.stx.kind or ""):
                continue
            # Keep the innermost node for a range (wrappers share their child's range).
            found[(a, b)] = {"text": text, "start": a, "end": b, "kind": nd.stx.kind,
                             "before": list(nd.goals_before), "after": list(nd.goals_after),
                             "uses": uses.get((a, b), [])}
    steps = sorted(found.values(), key=lambda s: (s["start"], (-s["end"][0], -s["end"][1])))
    for s in steps:
        span = (s["start"], s["end"])
        s["depth"] = sum(1 for o in steps if o["start"] <= s["start"] and s["end"] <= o["end"]
                         and (o["start"], o["end"]) != span)
        if s["text"].strip() == "]":  # `rw [...]` tries `rfl` after the last rule
            s["text"] = "rfl (attempted by rw after the last rule)"
    return steps


# =====================================================================================
# Running Lean
# =====================================================================================

def _info_json(resp: Any) -> dict[str, Any]:
    for m in getattr(resp, "messages", None) or []:
        data = m.data.strip()
        if m.severity == "info" and data.startswith("{"):
            return dict(json.loads(data))
    errors = [m.data for m in getattr(resp, "messages", None) or [] if m.severity == "error"]
    raise ProjectError("Lean did not answer the probe: "
                       + ("; ".join(errors)[:2000] or str(getattr(resp, "message", resp))[:2000]))


def _lean_str(s: str) -> str:
    return json.dumps(s, ensure_ascii=False)


def explain(
    item: Name | str,
    *,
    imports: Iterable[str] = (),
    project: object = None,
    timeout: float | None = None,
    refresh: bool = False,
) -> Explanation:
    """Explain a Lean/Mathlib proof step by step, exactly as Lean verified it.

    ``item`` is a name (``"Real.sin_sq_add_cos_sq"``), a catalog lemma or a ``pl.mathlib``
    reference. Runs the pinned Lean REPL: import the compiled module, re-elaborate the
    declaration's source file, compare the proof terms (see the module docstring). Slow the
    first time (the whole source file is re-checked); the result is cached.
    """
    from .backend.leaninteract import LeanRepl
    from .project import find_project

    name, mods = _target(item)
    modules = sorted({validate_qualified_name(m, "module") for m in (*mods, *imports)})
    proj = find_project(project)  # type: ignore[arg-type]
    proj.validate()
    key = hashlib.sha256(json.dumps([EXPLAIN_VERSION, name, modules, proj.config_hash(),
                                     proj.libraries_hash()]).encode()).hexdigest()[:24]
    cache = Path(proj.path) / ".pyleanx" / "explain" / f"{key}.json"
    if cache.exists() and not refresh:
        return from_json(json.loads(cache.read_text(encoding="utf-8")), proj)
    limit = timeout or max(proj.timeout, 3600)
    repl = LeanRepl(proj)  # private process: closed afterwards to free memory
    li = repl._li
    try:
        header = "\n".join(f"import {m}" for m in modules) or "import Mathlib"
        r1 = repl._run(li.Command(cmd=header + "\n" + _PROBE.replace("@@ROOT@@", _lean_str(name))),
                       limit)
        compiled = _info_json(r1)
        if "error" in compiled:
            raise ProjectError(f"Lean: {compiled['error']} (imports: {modules or ['Mathlib']})")
        if not compiled.get("range"):
            raise PyLeanXError(f"Lean has no source position for {name}")
        path, origin = source_file(proj, compiled["module"])
        text = path.read_text(encoding="utf-8")
        lines = text.splitlines()
        rng = compiled["range"]
        first, last = (rng["line"], rng["column"]), (rng["end_line"], rng["end_column"])

        r2 = repl._run(li.FileCommand(path=str(path.resolve()), all_tactics=True,
                                      infotree="original"), limit)
        replay_errors = [m.data for m in getattr(r2, "messages", None) or []
                         if m.severity == "error"]
        replayed: dict[str, Any] = {}
        if getattr(r2, "env", None) is not None:
            r3 = repl._run(li.Command(cmd=_PROBE.replace("@@ROOT@@", _lean_str(name)),
                                      env=r2.env), limit)
            replayed = _info_json(r3)
        steps = collect_steps(getattr(r2, "infotree", None) or [], getattr(r2, "tactics", []),
                              lines, first, last)

        step_lists = "#[" + ", ".join(
            "#[" + ", ".join(_lean_str(u) for u in s["uses"]) + "]" for s in steps) + "]"
        r4 = repl._run(li.Command(cmd=_LEMMAS.replace("@@ROOT@@", _lean_str(name))
                                  .replace("@@STEPS@@", step_lists), env=r1.env), limit)
        lemma_data = _info_json(r4)
    finally:
        repl.close()

    same_value = bool(compiled.get("value_hash")) and \
        replayed.get("value_hash") == compiled.get("value_hash")
    same_type = replayed.get("type_hash") == compiled.get("type_hash")
    exact = not replay_errors and same_value and same_type
    reason = ("" if exact else
              "the source did not re-elaborate cleanly: " + "; ".join(replay_errors)[:500]
              if replay_errors else
              "the re-elaborated proof term differs from the compiled one"
              if not same_value else "the re-elaborated statement differs")
    if origin.get("modified"):
        exact = False
        reason = "the source file is modified relative to its pinned revision"
    evidence = {**origin, "value_hash": compiled.get("value_hash"),
                "replayed_value_hash": replayed.get("value_hash"),
                "type_hash": compiled.get("type_hash"),
                "replayed_type_hash": replayed.get("type_hash"),
                "file_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
                "replay_errors": replay_errors[:5], "reason": reason}
    raw = {
        "name": name, "module": compiled["module"],
        "file": Path(*compiled["module"].split(".")).with_suffix(".lean").as_posix(),
        "first_line": first[0], "last_line": last[0], "statement": compiled.get("type", ""),
        "source": "\n".join(lines[first[0] - 1:last[0]]), "exact": exact, "evidence": evidence,
        "steps": [{"text": s["text"], "line": s["start"][0], "column": s["start"][1],
                   "depth": s["depth"], "goals_before": s["before"], "goals_after": s["after"],
                   "uses": u} for s, u in zip(steps, lemma_data["steps"], strict=True)],
        "cited": lemma_data["cited"],
        "lemmas": {d["name"]: d for d in lemma_data["lemmas"]},
    }
    cache.parent.mkdir(parents=True, exist_ok=True)
    cache.write_text(json.dumps(raw, ensure_ascii=False), encoding="utf-8")
    return from_json(raw, proj)


def from_json(raw: dict[str, Any], project: Any = None) -> Explanation:
    steps = tuple(ProofStep(s["text"], s["line"], s["column"], s["depth"],
                            tuple(s["goals_before"]), tuple(s["goals_after"]), tuple(s["uses"]))
                  for s in raw["steps"])
    lemmas = {n: LemmaInfo(d["name"], d["kind"], d["module"], d["type"])
              for n, d in raw["lemmas"].items()}
    return Explanation(raw["name"], raw["module"], raw["file"], raw["first_line"],
                       raw["last_line"], raw["statement"], raw["source"], raw["exact"],
                       dict(raw["evidence"]), steps, tuple(raw["cited"]), lemmas, project)

"""Library vendoring and generated bindings (no Lean needed)."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

import pyleanx as pl
from pyleanx import bindings as B
from pyleanx import libs as L
from pyleanx.project import LeanProject


def _project(tmp_path: Path) -> LeanProject:
    p = tmp_path / "proj"
    p.mkdir()
    (p / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
    (p / "lakefile.toml").write_text('name = "x"\n')
    (p / "lake-manifest.json").write_text(json.dumps(
        {"packages": [{"name": "mathlib", "rev": "d13f23b723b8a846827a245b89c10fc7d3f11612"}]}))
    return LeanProject.at(p)


def _source(tmp_path: Path, toolchain: str = "leanprover/lean4:v4.34.1") -> Path:
    src = tmp_path / "upstream" / "lean"
    (src / "Lib" / "Sub").mkdir(parents=True)
    (src / "lean-toolchain").write_text(toolchain + "\n")
    (src.parent / "LICENSE").write_text("Apache License 2.0 (test)")
    (src / "Lib" / "A.lean").write_text(
        "/- Copyright -/\nmodule\n\npublic import Mathlib.Analysis.Real.Sqrt\n"
        "import Lib.Sub.B -- helper\n\nnamespace Lib\ndef a : Nat := 1\nend Lib\n")
    (src / "Lib" / "Sub" / "B.lean").write_text("import Mathlib\n\ndef b : Nat := 2\n")
    (src / "Lib" / "Unused.lean").write_text("import Lib.A\n")
    return src


def test_module_imports_parses_lean_headers():
    text = ("/-! doc\nimport Fake -/\n-- import Fake2\nmodule\npublic import A.B\n"
            "meta import C\nimport D E\n\nimport NotHeader -- after code? no\ndef x := 1\n"
            "import Late\n")
    assert L.module_imports(text) == ["A.B", "C", "D", "E", "NotHeader"]


def test_add_local_library_vendors_the_import_closure(tmp_path):
    proj = _project(tmp_path)
    src = _source(tmp_path)
    lib = L.add_library("demo", str(src.parent), subdir="lean", roots=["Lib.A"], project=proj,
                        build=False, progress=lambda *_: None)
    assert lib.modules == ["Lib.Sub.B", "Lib.A"]  # dependencies first, unused not vendored
    vendored = lib.src_dir(proj.path)
    assert (vendored / "Lib" / "A.lean").exists() and not (vendored / "Lib" / "Unused.lean").exists()
    notice = (lib.root_dir(proj.path) / "NOTICE.txt").read_text(encoding="utf-8")
    assert "Apache License 2.0 (test)" in notice
    assert [x.name for x in L.list_libraries(proj)] == ["demo"]
    h1 = L.libraries_hash(proj.path)
    assert h1 and proj.libraries_hash() == h1
    L.remove_library("demo", proj)
    assert L.list_libraries(proj) == [] and L.libraries_hash(proj.path) == ""


def test_missing_modules_and_version_mismatches_are_reported(tmp_path):
    proj = _project(tmp_path)
    src = _source(tmp_path)
    (src / "Lib" / "C.lean").write_text("import OtherPackage.Thing\n")
    with pytest.raises(L.LibraryError, match="OtherPackage.Thing"):
        L.add_library("demo", str(src.parent), subdir="lean", roots=["Lib.C"], project=proj,
                      build=False, progress=lambda *_: None)
    other = tmp_path / "old"
    old_src = _source(other, toolchain="leanprover/lean4:v4.20.0")
    with pytest.raises(L.LibraryError, match="toolchain"):
        L.add_library("old", str(old_src.parent), subdir="lean", roots=["Lib.A"], project=proj,
                      build=False, progress=lambda *_: None)


def test_library_paths_are_added_to_lean_path(tmp_path, monkeypatch):
    proj = _project(tmp_path)
    src = _source(tmp_path)
    L.add_library("demo", str(src.parent), subdir="lean", roots=["Lib.A"], project=proj,
                  build=False, progress=lambda *_: None)
    monkeypatch.setattr(LeanProject, "_lake_env_base",
                        lambda self, refresh=False, timeout=900.0: {"LEAN": "lean",
                                                                    "LEAN_PATH": "/mathlib"})
    env = proj.lake_env()
    first = env["LEAN_PATH"].split(__import__("os").pathsep)[0]
    assert first.endswith(str(Path(".pyleanx") / "libs" / "demo" / "build"))
    assert env["LEAN_PATH"].endswith("/mathlib")


def test_unsafe_lean_options_are_rejected(tmp_path):
    proj = _project(tmp_path)
    src = _source(tmp_path)
    with pytest.raises(L.LibraryError):
        L.add_library("demo", str(src.parent), subdir="lean", roots=["Lib.A"], project=proj,
                      build=False, lean_options=[("autoImplicit", "false; rm")],
                      progress=lambda *_: None)


# ------------------------------------------------------------------------------ bindings
def _decl(name, kind="def", binders=(), result="ℝ", is_proof=False, result_is_type=False,
          result_is_prop=False, fields=(), module="Lib.A"):
    return B.Decl(name, module, kind, "T", tuple(binders), result, result_is_prop,
                  result_is_type, is_proof, tuple(fields), None)


def test_declarations_become_python_objects(monkeypatch):
    decls = [
        _decl("Lib.Vec", result="Type", result_is_type=True),
        _decl("Lib.Datum", kind="inductive", result="Type", result_is_type=True,
              fields=("f₀", "E")),
        _decl("Lib.Datum.f₀", binders=[("self", "explicit", "Lib.Datum")], result="ℝ"),
        _decl("Lib.Datum.E", binders=[("self", "explicit", "Lib.Datum"),
                                      ("a✝", "explicit", "Lib.Vec")], result="Lib.Vec"),
        _decl("Lib.q", binders=[("v", "explicit", "Lib.Vec")], result="ℝ"),
        _decl("Lib.Good", binders=[("d", "explicit", "Lib.Datum")], result="Prop",
              result_is_prop=True),
        _decl("Lib.one_le_q", kind="theorem", binders=[("v", "explicit", "Lib.Vec")],
              result="1 ≤ Lib.q v", is_proof=True),
        _decl("Lib.dep", binders=[("n", "explicit", "ℕ"), ("x", "explicit", "Fin n")],
              result="Fin n"),
    ]
    monkeypatch.setattr(B, "export_declarations", lambda mods, project=None, **kw: decls)
    root = B.use("Lib.A")
    Lib = root.Lib
    assert isinstance(Lib.Vec, pl.LeanType) and Lib.Vec.lean == "Lib.Vec"
    d = pl.var("d", Lib.Datum)
    assert d.f0.to_lean() == "d.f₀" and d.f0.sort is pl.Real  # ASCII alias for f₀
    assert d.E.sort == pl.Fn(Lib.Vec, Lib.Vec)  # telescoped field type is a function
    v = pl.var("v", Lib.Vec)
    assert Lib.q(v).sort is pl.Real and Lib.q(v).to_lean() == "Lib.q v"
    assert Lib.Good(d).sort is pl.Prop
    lemma = Lib.one_le_q
    assert isinstance(lemma, pl.proofs.Name) and lemma.imports == ("Lib.A",)
    t = pl.Theorem("t", [v], conclusion=pl.Le(1, Lib.q(v)), proof=pl.exact(lemma(v)))
    assert "import Lib.A" in t.to_lean() and "exact Lib.one_le_q v" in t.to_lean()
    assert Lib.dep(pl.nat(3), pl.var("k", pl.Fin(3))).sort is pl.UNKNOWN  # dependent result
    assert "q" in dir(Lib) and "Datum" in dir(Lib)
    with pytest.raises(AttributeError):
        Lib.nope  # noqa: B018
    assert B.get("Lib.q") is Lib.q and B.search("one_le")[0].name == "Lib.one_le_q"


def test_write_bindings_module(tmp_path, monkeypatch):
    decls = [_decl("Lib.q", binders=[("v", "explicit", "ℝ")], result="ℝ"),
             _decl("Lib.Sub.r", result="ℝ")]
    monkeypatch.setattr(B, "export_declarations", lambda mods, project=None, **kw: decls)
    out = B.write_bindings(["Lib.A"], tmp_path / "lib_bindings.py")
    text = out.read_text(encoding="utf-8")
    assert "class Lib:" in text and "q = _get('Lib.q')" in text and "class Sub:" in text
    compile(text, "lib_bindings.py", "exec")


def test_sort_from_text():
    assert B.sort_from_text("ℝ", ()) is pl.Real and B.sort_from_text("Prop", ()) is pl.Prop
    assert B.sort_from_text("Fin n", (), ["n"]) is pl.UNKNOWN
    assert B.sort_from_text("Set ℝ", ("M",)).lean == "Set ℝ"
    assert B.sort_from_text("ℝ) (h : False", ()) is pl.UNKNOWN  # unsafe text never splices


def test_cli_parsers():
    from pyleanx.cli import build_parser

    p = build_parser()
    a = p.parse_args(["add", "oai", "https://github.com/openai/math", "--rev", "abc",
                      "--subdir", "lean", "--module", "M.A", "--module", "M.B"])
    assert a.module == ["M.A", "M.B"] and a.subdir == "lean"
    assert p.parse_args(["bindings", "M.A", "-o", "x.py"]).output == "x.py"
    assert p.parse_args(["libs"]).func.__name__ == "cmd_libs"

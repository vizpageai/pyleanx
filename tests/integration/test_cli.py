"""CLI tests. `show-lean`/`compile` need no Lean; `check`/`doctor` use the real toolchain."""

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]


def run_cli(*args, env_extra=None):
    env = dict(os.environ)
    env["PYTHONIOENCODING"] = "utf-8"
    env.update(env_extra or {})
    return subprocess.run([sys.executable, "-m", "pyleanx.cli", *args], cwd=ROOT,
                          capture_output=True, text=True, encoding="utf-8", env=env,
                          timeout=900)


def test_show_lean():
    p = run_cli("show-lean", "examples/square_identity.py")
    assert p.returncode == 0, p.stderr
    assert "theorem square_identity (x y : Real) :" in p.stdout
    assert "#print axioms square_identity" in p.stdout


def test_compile_writes_file(tmp_path):
    out = tmp_path / "out.lean"
    p = run_cli("compile", "examples/nat_add_zero.py", "-o", str(out))
    assert p.returncode == 0, p.stderr
    assert "NOT verified" in p.stdout
    assert "theorem nat_add_zero (n : Nat) :" in out.read_text(encoding="utf-8")


def test_bad_script_reports_error(tmp_path):
    script = tmp_path / "empty.py"
    script.write_text("x = 1\n", encoding="utf-8")
    p = run_cli("show-lean", str(script))
    assert p.returncode == 2 and "THEOREMS" in p.stderr


def test_cache_commands(tmp_path):
    env = {"PYLEANX_CACHE_DIR": str(tmp_path)}
    assert run_cli("cache", "stats", env_extra=env).returncode == 0
    p = run_cli("cache", "clear", env_extra=env)
    assert p.returncode == 0 and "removed 0" in p.stdout


@pytest.mark.lean
def test_check_valid_and_invalid(lean_project, tmp_path):
    env = {"PYLEANX_CACHE_DIR": str(tmp_path)}
    ok = run_cli("check", "examples/square_identity.py", env_extra=env)
    assert ok.returncode == 0, ok.stdout + ok.stderr
    assert "1/1 verified" in ok.stdout
    bad = run_cli("check", "examples/bad_proof.py", env_extra=env)
    assert bad.returncode == 1, bad.stdout + bad.stderr
    assert "0/2 verified" in bad.stdout


@pytest.mark.lean
def test_check_json(lean_project, tmp_path):
    p = run_cli("check", "examples/implication.py", "--json",
                env_extra={"PYLEANX_CACHE_DIR": str(tmp_path)})
    assert p.returncode == 0, p.stdout + p.stderr
    data = json.loads(p.stdout)
    assert [d["theorem"] for d in data] == ["identity_imp", "sum_pos"]
    assert all(d["verified"] and d["schema_version"] == 1 for d in data)
    assert "lean_source" not in data[0]


@pytest.mark.lean
def test_ai_batch_example_raw_tactics(lean_project, tmp_path):
    p = run_cli("check", "examples/ai_batch.py", "--json", "--allow-raw-tactics",
                env_extra={"PYLEANX_CACHE_DIR": str(tmp_path)})
    data = {d["theorem"]: d for d in json.loads(p.stdout)}
    assert data["cand_ring"]["status"] == "rejected"
    assert data["cand_positivity"]["verified"]
    assert data["cand_llm_text"]["verified"] and data["cand_llm_text"]["raw_tactics_used"]
    assert p.returncode == 1  # not all candidates verified
    p2 = run_cli("check", "examples/ai_batch.py", "--json",
                 env_extra={"PYLEANX_CACHE_DIR": str(tmp_path)})
    data2 = {d["theorem"]: d for d in json.loads(p2.stdout)}
    assert data2["cand_llm_text"]["status"] == "policy_rejected"


@pytest.mark.lean
def test_doctor(lean_project):
    p = run_cli("doctor", "--json")
    data = json.loads(p.stdout)
    failing = [c for c in data["checks"] if not c["ok"]]
    assert p.returncode == 0 and data["ok"], failing

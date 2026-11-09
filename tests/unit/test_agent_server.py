"""JSON-lines agent server and the bank/agent CLI (fake REPL, no Lean)."""

from __future__ import annotations

import io
import json
from pathlib import Path

import pytest
from test_session import FakeRepl

import pyleanx as pl
from pyleanx import session as session_mod
from pyleanx.agent.server import AgentServer
from pyleanx.cli import main

PROJECT = Path(__file__).resolve().parents[2] / "lean-project"


@pytest.fixture
def fake(monkeypatch):
    repl = FakeRepl()
    monkeypatch.setattr(session_mod, "get_repl", lambda project, launch: repl)
    return repl


def _imp_canonical():
    P = pl.prop_symbol("P")
    return pl.Theorem("imp", [P], conclusion=pl.Implies(P, P),
                      proof=pl.ring()).canonical()


def _run(server, *reqs):
    inp = io.StringIO("\n".join(json.dumps(r) if isinstance(r, dict) else r for r in reqs))
    out = io.StringIO()
    server.serve(inp, out)
    return [json.loads(x) for x in out.getvalue().splitlines()]


def test_server_session_flow(fake):
    resps = _run(AgentServer(PROJECT),
                 {"id": 1, "method": "tools"},
                 {"id": 2, "method": "call", "params": {"name": "get_state"}},
                 {"id": 3, "method": "open", "params": {"theorem": _imp_canonical()}},
                 {"id": 4, "method": "call",
                  "params": {"name": "apply_tactic", "arguments": {"tactic": "intro h"}}},
                 {"id": 5, "method": "call",
                  "params": {"name": "apply_tactic", "arguments": {"tactic": "exact h"}}},
                 {"id": 6, "method": "transcript"},
                 "not json",
                 {"id": 7, "method": "close"})
    assert [t["name"] for t in resps[0]["result"]][1] == "apply_tactic"
    assert "error" in resps[1]  # no open theorem yet
    assert resps[2]["result"]["goals"] == ["⊢ goal"]
    assert resps[2]["result"]["history"] == []  # the client's proof was dropped
    assert resps[3]["result"]["ok"] and resps[4]["result"]["complete"]
    assert resps[5]["result"][0]["event"] == "open"
    assert resps[6]["id"] is None and "bad request" in resps[6]["error"]
    assert resps[7]["result"] == {"closed": True}


def test_server_client_cannot_enable_raw(fake):
    resps = _run(AgentServer(PROJECT),
                 {"id": 1, "method": "open",
                  "params": {"theorem": _imp_canonical(), "allow_raw": True}},
                 {"id": 2, "method": "call",
                  "params": {"name": "apply_tactic", "arguments": {"tactic": "intro h; exact h"}}})
    assert not resps[1]["result"]["ok"] and "raw" in resps[1]["result"]["error"]


def test_server_rejects_malformed_theorems(fake):
    bad = _imp_canonical()
    bad["conclusion"] = ["eq", ["var", "zzz", "Real"], ["var", "zzz", "Real"]]
    resps = _run(AgentServer(PROJECT), {"id": 1, "method": "open", "params": {"theorem": bad}})
    assert "SerializationError" in resps[0]["error"]


def test_cli_agent_export(tmp_path, capsys):
    out = tmp_path / "b.jsonl"
    assert main(["agent", "export", "-o", str(out)]) == 0
    assert len(out.read_text(encoding="utf-8").splitlines()) == len(pl.agent.basic())


def test_cli_bank_search_and_show(tmp_path, capsys, monkeypatch):
    path = tmp_path / "bank.json"
    bank = pl.TheoremBank(path)
    form = pl.Formalization("lean4", "mathlib", "t", "r")
    bank.add_declaration("geometry.tri", "dist_triangle", "dist x z ≤ dist x y + dist y z",
                         form, aliases=("triangle inequality",))
    bank.save()
    assert main(["bank", "search", "triangle", "--bank", str(path)]) == 0
    assert "geometry.tri" in capsys.readouterr().out
    assert main(["bank", "show", "triangle inequality", "--bank", str(path), "--json"]) == 0
    assert json.loads(capsys.readouterr().out)["lean_name"] == "dist_triangle"
    assert main(["bank", "search", "zzz", "--bank", str(path)]) == 1
    assert main(["bank", "list", "--bank", str(path)]) == 0
    assert main(["bank", "show", "--bank", str(path)]) == 2

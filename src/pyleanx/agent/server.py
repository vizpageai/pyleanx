"""JSON-lines protocol over stdin/stdout, for agents written in any language.

Request:  ``{"id": 1, "method": "open", "params": {"theorem": <canonical theorem JSON>}}``
Response: ``{"id": 1, "result": {...}}`` or ``{"id": 1, "error": "message"}``

Methods: ``open`` (theorem -> observation), ``tools`` (JSON schemas), ``call``
(``{"name": "apply_tactic", "arguments": {"tactic": "ring"}}``), ``transcript``, ``close``.

Theorems arrive as data (canonical JSON, rebuilt strictly; any proof is dropped).
Whether free-form (raw) tactic text may run is decided by the *operator*
(``pyleanx agent serve --allow-raw``), never by the client.
"""

from __future__ import annotations

import json
import sys
from typing import IO, Any

from ..errors import PyLeanXError
from ..project import LeanProject, find_project
from .env import TOOLS, ProofEnv


class AgentServer:
    def __init__(self, project: LeanProject | str | None = None, *, allow_raw: bool = False,
                 env_factory: Any = ProofEnv) -> None:
        self.project = find_project(project)
        self.allow_raw = allow_raw
        self.env_factory = env_factory
        self.env: ProofEnv | None = None

    def handle(self, req: dict[str, Any]) -> dict[str, Any]:
        rid = req.get("id")
        try:
            return {"id": rid, "result": self._dispatch(req.get("method"),
                                                        req.get("params") or {})}
        except (PyLeanXError, KeyError, TypeError, ValueError) as exc:
            return {"id": rid, "error": f"{type(exc).__name__}: {exc}"}

    def _dispatch(self, method: Any, params: dict[str, Any]) -> Any:
        from ..serialize import theorem_from_canonical

        if method == "tools":
            return TOOLS
        if method == "open":
            data = dict(params["theorem"])
            data["proof"] = None
            thm = theorem_from_canonical(data)
            self.env = self.env_factory(thm, self.project, allow_raw=self.allow_raw)
            return self.env.observe()
        if self.env is None:
            raise ValueError("no open theorem; call `open` first")
        if method == "call":
            return self.env.call_tool(params["name"], params.get("arguments") or {})
        if method == "transcript":
            return self.env.transcript
        if method == "close":
            self.env = None
            return {"closed": True}
        raise ValueError(f"unknown method {method!r}")

    def serve(self, inp: IO[str] = sys.stdin, out: IO[str] = sys.stdout) -> int:
        for line in inp:
            line = line.strip()
            if not line:
                continue
            try:
                req = json.loads(line)
                if not isinstance(req, dict):
                    raise ValueError("request must be a JSON object")
            except ValueError as exc:
                resp: dict[str, Any] = {"id": None, "error": f"bad request: {exc}"}
            else:
                resp = self.handle(req)
            out.write(json.dumps(resp, ensure_ascii=False, default=str) + "\n")
            out.flush()
        return 0

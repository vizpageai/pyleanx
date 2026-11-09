"""Local cache of *verified* results only, keyed by a full reproducibility fingerprint."""

from __future__ import annotations

import json
import os
import sqlite3
import time
from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path

from .interface import Status, VerificationResult


def default_cache_dir() -> Path:
    env = os.environ.get("PYLEANX_CACHE_DIR")
    if env:
        return Path(env)
    return Path.home() / ".cache" / "pyleanx"


class ResultCache:
    """On-disk cache of *verified* results only, keyed by the reproducibility fingerprint."""

    def __init__(self, directory: Path | None = None) -> None:
        self.directory = directory or default_cache_dir()
        self.path = self.directory / "results.sqlite"

    @contextmanager
    def _connect(self) -> Iterator[sqlite3.Connection]:
        self.directory.mkdir(parents=True, exist_ok=True)
        con = sqlite3.connect(self.path)
        try:
            con.execute(
                "CREATE TABLE IF NOT EXISTS results (fingerprint TEXT PRIMARY KEY, theorem TEXT, "
                "created REAL, payload TEXT)"
            )
            yield con
            con.commit()
        finally:
            con.close()

    def get(self, fingerprint: str) -> VerificationResult | None:
        if not self.path.exists():
            return None
        with self._connect() as con:
            row = con.execute(
                "SELECT payload FROM results WHERE fingerprint = ?", (fingerprint,)
            ).fetchone()
        if row is None:
            return None
        result = VerificationResult.from_dict(json.loads(row[0]))
        if result.status is not Status.VERIFIED or result.fingerprint != fingerprint:
            return None  # defensive: never serve anything but a matching verified result
        result.cache_hit = True
        return result

    def put(self, result: VerificationResult) -> None:
        if result.status is not Status.VERIFIED or not result.fingerprint:
            return
        payload = result.to_dict()
        payload["cache_hit"] = False
        with self._connect() as con:
            con.execute(
                "INSERT OR REPLACE INTO results VALUES (?, ?, ?, ?)",
                (result.fingerprint, result.theorem, time.time(), json.dumps(payload)),
            )

    def stats(self) -> dict:
        if not self.path.exists():
            return {"path": str(self.path), "entries": 0}
        with self._connect() as con:
            (n,) = con.execute("SELECT COUNT(*) FROM results").fetchone()
        return {"path": str(self.path), "entries": n, "bytes": self.path.stat().st_size}

    def clear(self) -> int:
        if not self.path.exists():
            return 0
        with self._connect() as con:
            (n,) = con.execute("SELECT COUNT(*) FROM results").fetchone()
            con.execute("DELETE FROM results")
        return n

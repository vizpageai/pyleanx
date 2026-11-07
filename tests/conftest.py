import os
import sys

import pytest

from pyleanx.project import find_project

# Generated Lean contains Unicode; keep Windows consoles from choking on it.
for _stream in (sys.stdout, sys.stderr):
    try:
        _stream.reconfigure(encoding="utf-8")
    except (AttributeError, ValueError):
        pass


@pytest.fixture(autouse=True)
def _isolated_cache(tmp_path, monkeypatch):
    """Never let tests read or pollute the user's result cache."""
    monkeypatch.setenv("PYLEANX_CACHE_DIR", str(tmp_path / "pyleanx-cache"))


def _lean_project_or_reason():
    proj = find_project()
    try:
        proj.validate()
    except Exception as exc:  # noqa: BLE001
        return None, f"no pinned Lean project: {exc}"
    if proj.lake_executable() is None:
        return None, "lake not on PATH"
    if not proj.mathlib_cache_present():
        return None, f"Mathlib cache missing in {proj.path} (run `lake exe cache get`)"
    return proj, ""


@pytest.fixture(scope="session")
def lean_project():
    proj, reason = _lean_project_or_reason()
    if proj is None:
        if os.environ.get("PYLEANX_REQUIRE_LEAN") == "1":
            pytest.fail(reason)
        pytest.skip(reason)
    # Generous timeout: cold Mathlib loads on a busy laptop can exceed the 300 s default.
    return proj.with_(timeout=900)

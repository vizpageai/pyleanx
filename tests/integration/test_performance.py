"""Timing measurements (reported, loosely bounded). Not a benchmark suite.

Run with `-s` to see the numbers; docs/roadmap.md records measured values.
"""

import time
import uuid

import pytest

import pyleanx as pl
from pyleanx.backend.subprocess_backend import run_lean

pytestmark = pytest.mark.lean


def test_overhead_vs_direct_lean(lean_project):
    x, y = pl.symbols("x y", pl.Real)
    thm = pl.Theorem("perf_ring", [x, y], conclusion=(x + y) ** 2 == x**2 + 2 * x * y + y**2,
                     proof=pl.ring())
    src = thm.to_lean()
    work = lean_project.path / ".pyleanx" / "perf"
    work.mkdir(parents=True, exist_ok=True)
    f = work / f"Perf_{uuid.uuid4().hex}.lean"
    f.write_text(src, encoding="utf-8", newline="\n")
    run_lean(lean_project, f, timeout=600)  # warm OS file cache
    t0 = time.perf_counter()
    direct = run_lean(lean_project, f, timeout=600)
    t_direct = time.perf_counter() - t0
    f.unlink(missing_ok=True)

    t0 = time.perf_counter()
    r = thm.verify(lean_project, use_cache=False)
    t_pyleanx = time.perf_counter() - t0

    thm.verify(lean_project)  # populate the cache (use_cache=False neither reads nor writes)
    t0 = time.perf_counter()
    cached = thm.verify(lean_project)
    t_cached = time.perf_counter() - t0

    many = [pl.Theorem(f"perf_batch_{i}", [x], conclusion=(x + i) ** 2 >= 0,
                       proof=pl.positivity()) for i in range(10)]
    t0 = time.perf_counter()
    batch = pl.verify_all(many, project=lean_project, use_cache=False)
    t_batch = time.perf_counter() - t0

    print(f"\n[perf] direct lake env lean: {t_direct:.2f}s; pyleanx verify: {t_pyleanx:.2f}s; "
          f"cached: {t_cached * 1000:.1f}ms; batch of 10: {t_batch:.2f}s")
    assert direct.returncode == 0 and r.verified and cached.cache_hit
    assert all(b.verified for b in batch)
    assert t_pyleanx < t_direct + 10  # Python-side overhead stays small

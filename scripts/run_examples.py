"""Run every example against the real pinned Lean and check its expected outcome.

Release gate (see IMPLEMENTATION_PLAN.md §10: "All included examples execute successfully
in the pinned environment"). Usage:  python scripts/run_examples.py [name ...]
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "examples"

# name -> (command, expected exit code). `check` scripts go through the CLI.
CHECK = [sys.executable, "-m", "pyleanx", "check"]
RUN = [sys.executable]
CASES: dict[str, tuple[list[str], int]] = {
    "square_identity": (CHECK, 0),
    "square_nonnegative": (CHECK, 0),
    "nat_add_zero": (CHECK, 0),
    "implication": (CHECK, 0),
    "decorator_and_latex": (CHECK, 0),
    "bad_proof": (CHECK, 1),  # must be rejected
    "ai_batch": (RUN, 0),  # checks its own expected statuses
    "domains": (RUN, 0),
    "theorem_bank": (RUN, 0),
    "interactive_session": (RUN, 0),
    "agent_search": (RUN, 0),
    "vlasov_maxwell_kinematics": (RUN, 0),
    "oai_ceil_residue": (RUN, 0),
    "theorem_families": (RUN, 0),  # checks that the bad row is rejected
    "side_splitter": (RUN, 0),
    "side_splitter_vectors": (RUN, 0),
    "readable_trig": (RUN, 0),
    "readable_side_splitter": (RUN, 0),
    "readable_am_gm": (RUN, 0),
    "readable_infinite_primes": (RUN, 0),
    "readable_consecutive_even": (RUN, 0),
    "readable_limit_sum": (RUN, 0),
    "readable_group_abelian": (RUN, 0),
    "readable_bernoulli": (RUN, 0),
    "readable_cauchy_integral": (RUN, 0),
    "using_cauchy_integral": (RUN, 0),
    "readable_angle_bisector": (RUN, 0),
    "textbook_geometry": (RUN, 0),
    "geometry_lecture": (RUN, 0),
    "analysis_lecture": (RUN, 0),
    "harmonic_lecture": (RUN, 0),
    "singular_integrals": (RUN, 0),  # Stein ch. I §1: covering, maximal function
    "marcinkiewicz": (RUN, 0),  # the Lp bound for the maximal function
    "hilbert_transform": (RUN, 0),  # the Hilbert transform on L2
    "calderon_zygmund": (RUN, 0),  # the Calderón–Zygmund decomposition
    "hilbert_kernel": (RUN, 0),  # the Hilbert kernel away from its singularity
    "cz_intervals": (RUN, 0),  # the intervals of {Mf > α}
    "pythagoras_similar": (RUN, 0),  # Pythagoras from similar triangles
    "euclid_book1": (RUN, 0),  # Euclid I: angles, exterior angle, midsegment
}

# Examples deliberately not run here, with the reason (each must be run by hand).
SKIPPED: dict[str, str] = {
    "oai_vlasov_maxwell": "needs `pyleanx add` of openai/math (vendored library build, "
                          "~12 min) and ~20 min per Lean check; see docs/roadmap.md",
}

# Modules the lecture notebooks import; they state no theorems of their own.
HELPERS = {
    "lecture_tools",      # check(...) and failed-step reporting for the notebooks
    "singular_lecture",   # figures for lecture_singular_integrals.ipynb (unit-tested)
}


def annotate(title: str, message: str) -> None:
    """On GitHub Actions, report a failure as an annotation (readable without the logs)."""
    if os.environ.get("GITHUB_ACTIONS") != "true":
        return

    def esc(s: str) -> str:
        return s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")

    title = esc(title).replace(",", "%2C").replace(":", "%3A")
    print(f"::error title={title}::{esc(message)}", flush=True)


def unclassified() -> list[str]:
    """Example scripts with neither an expected outcome nor a reason to skip them."""
    return sorted(p.stem for p in EXAMPLES.glob("*.py")
                  if p.stem not in CASES and p.stem not in SKIPPED and p.stem not in HELPERS)


def main(argv: list[str]) -> int:
    for name, why in SKIPPED.items():
        print(f"skip {name}: {why}")
    missing = unclassified()
    if missing:
        print(f"examples without an expected outcome: {missing}")
        annotate("run_examples", f"examples without an expected outcome: {missing}")
        return 2
    names = argv or list(CASES)
    failures = []
    for name in names:
        cmd, want = CASES[name]
        t0 = time.monotonic()
        proc = subprocess.run([*cmd, str(EXAMPLES / f"{name}.py")], cwd=ROOT,
                              capture_output=True, text=True, encoding="utf-8")
        ok = proc.returncode == want
        print(f"{'ok ' if ok else 'FAIL'} {name:22s} exit={proc.returncode} (want {want}) "
              f"{time.monotonic() - t0:6.1f}s", flush=True)
        if not ok:
            failures.append(name)
            print(proc.stdout[-4000:], proc.stderr[-4000:], sep="\n")
            annotate(f"example {name}", f"exit {proc.returncode} (want {want})\n"
                     + (proc.stdout[-1500:] + "\n" + proc.stderr[-1500:]).strip())
    print(f"{len(names) - len(failures)}/{len(names)} examples behaved as expected")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

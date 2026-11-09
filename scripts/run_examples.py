"""Run every example against the real pinned Lean and check its expected outcome.

Release gate (see IMPLEMENTATION_PLAN.md §10: "All included examples execute successfully
in the pinned environment"). Usage:  python scripts/run_examples.py [name ...]
"""

from __future__ import annotations

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
}


def main(argv: list[str]) -> int:
    missing = sorted(p.stem for p in EXAMPLES.glob("*.py") if p.stem not in CASES)
    if missing:
        print(f"examples without an expected outcome: {missing}")
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
    print(f"{len(names) - len(failures)}/{len(names)} examples behaved as expected")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

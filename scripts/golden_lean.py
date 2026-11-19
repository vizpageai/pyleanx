"""Golden Lean: the fingerprint of the generated Lean of every written proof in the benchmark.

    python scripts/golden_lean.py            # report proofs whose generated Lean changed
    python scripts/golden_lean.py --update   # record the current fingerprints

A refactoring of the core must leave these unchanged. A deliberate change of generated Lean
is recorded with --update only after the affected proofs were re-verified with Lean
(``python benchmarks/naturalness.py --lean --only <module>``).
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GOLDEN = ROOT / "tests" / "golden" / "lean_fingerprints.json"


def current() -> dict[str, str]:
    for p in (ROOT / "benchmarks", ROOT / "examples"):
        if str(p) not in sys.path:
            sys.path.insert(0, str(p))
    import naturalness

    return {f"{mod}.{t.name}": hashlib.sha256(t.to_lean().encode()).hexdigest()[:16]
            for _, mod, t in naturalness.collect()}


def changed() -> list[str]:
    want = json.loads(GOLDEN.read_text(encoding="utf-8"))
    got = current()
    return sorted(k for k in set(want) | set(got) if want.get(k) != got.get(k))


def main(argv: list[str]) -> int:
    if "--update" in argv:
        GOLDEN.parent.mkdir(parents=True, exist_ok=True)
        text = json.dumps(current(), indent=1, sort_keys=True)
        GOLDEN.write_text(text + "\n", encoding="utf-8", newline="\n")
        print(f"recorded {GOLDEN.relative_to(ROOT)}")
        return 0
    diff = changed()
    for k in diff:
        print(f"changed: {k}")
    print(f"{len(diff)} proof(s) with changed generated Lean")
    return 1 if diff else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

"""Shared by the lecture notebooks: check a proof with Lean and say which step failed."""

from __future__ import annotations

import re
from typing import Any

import pyleanx as pl

_SPAN = re.compile(r"^step (\d+):")


def failed_steps(thm: pl.Theorem, result: Any) -> list[int]:
    """Numbers of the proof's steps (as printed) that Lean rejected; 0 = the final "Hence"."""
    steps = list(thm.proof.flat()) if thm.proof is not None else []
    found: set[int] = set()
    for d in result.errors:
        m = _SPAN.match(d.span_label or "")
        if not m:
            continue
        k = int(m.group(1))
        is_last = k == len(steps) and type(steps[-1]).__name__ == "Conclude"
        found.add(0 if is_last else k)
    return sorted(found)


def describe(numbers: list[int]) -> str:
    names = [f"**step {k}**" for k in numbers if k] + (
        ["the **final step** (*Hence …*)"] if 0 in numbers else [])
    return ", ".join(names)


def check(thm: pl.Theorem | None, *, timeout: float = 1800, hint: str = "",
          timeout_hint: str = "") -> Any:
    """Check a proof with Lean and show it as a readable proof.

    ✅ means Lean's kernel accepted every step and the axiom audit passed (standard axioms
    only). When Lean rejects the proof, the steps it could not justify are named.
    """
    from IPython.display import Markdown, display

    if thm is None or thm.proof is None:
        display(Markdown("✏️ *Write your steps first:* put the steps of your proof inside "
                         "the exercise call, then run the cell again."))
        return None
    display(Markdown("⏳ *Lean is checking this proof (the first check of a session takes a "
                     "minute or more; a proof that was already checked comes back at once)…*"))
    result = thm.verify(timeout=timeout)
    display(Markdown(thm.prose(result).to_markdown()))
    if result.verified:
        display(Markdown(f"✅ **Lean accepted the proof.** Axioms used: "
                         f"`{', '.join(result.axioms or ()) or 'none'}` (the standard ones)."))
        return result
    tips = ["❌ **Lean did not accept this proof.**"]
    bad = failed_steps(thm, result)
    if bad:
        tips.append(f"Lean could not justify {describe(bad)} from the reasons given.")
        first = next((d for d in result.errors if _SPAN.match(d.span_label or "")), None)
        if first is not None:
            msg = first.message.split("\n")[0][:240]
            tips.append(f"Lean's own words: `{msg}`")
        tips.append(hint or "Check that the step is really true at that point of the proof "
                    "and that the cited facts (with the earlier steps) give it.")
    elif any("heartbeats" in d.message for d in result.errors):
        tips.append("Lean ran out of time looking for a justification: usually one step "
                    "does not follow from its reasons. Split a long step into smaller ones. "
                    + timeout_hint)
    else:
        first = next(iter(result.errors), None)
        if first is not None:
            tips.append(f"Lean says: `{first.message.splitlines()[0][:300]}`")
    display(Markdown("\n\n".join(tips)))
    return result


def check_all(theorems: list[pl.Theorem], *, timeout: float = 3600) -> list[Any]:
    """Check several theorems in one Lean run (they may cite each other) and show each."""
    from IPython.display import Markdown, display

    display(Markdown(f"⏳ *Lean is checking {len(theorems)} theorems in one file…*"))
    results = pl.verify_all(theorems, timeout=timeout)
    for thm, res in zip(theorems, results, strict=True):
        display(Markdown(thm.prose(res).to_markdown()))
        if not res.verified:
            bad = failed_steps(thm, res)
            display(Markdown(f"❌ Lean could not justify {describe(bad) or 'this proof'}."))
    ok = sum(r.verified for r in results)
    display(Markdown(f"**{ok} of {len(theorems)} theorems accepted by Lean** "
                     "(standard axioms only)." if ok == len(theorems) else
                     f"**{ok} of {len(theorems)} theorems accepted.**"))
    return results

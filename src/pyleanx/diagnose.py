"""Why a proof was not accepted, in the words of the proof (not Lean's).

    res = thm.check()                    # or thm.verify()
    for line in pl.explain_failure(thm, res):
        print(line)

Each Lean error is attributed to the step it belongs to and restated: which step, what it
claims, what it was justified by, what Lean still had to show (as a goal), and a hint for
the usual causes. A numeric sanity check runs first: a step that is false on a sample is
reported as false, with the numbers, before anything else. The original Lean messages stay
in ``res.diagnostics``.
"""

from __future__ import annotations

import re
from typing import Any

_HINTS: list[tuple[str, str]] = [
    (r"linarith failed", "the step is not a linear consequence of the cited facts; cite the "
     "fact that supplies the missing product or inequality, or split the step in two"),
    (r"(deterministic\) timeout|maximum number of heartbeats|maximum recursion depth)",
     "Lean ran out of time looking for a justification; state the step in the same "
     "orientation as the cited fact (A ≠ C, not C ≠ A), cite fewer facts, or split it"),
    (r"Unknown (identifier|constant)", "a cited name is not known: check its spelling and "
     "that the step it names comes earlier"),
    (r"type mismatch", "the cited fact does not have the shape of the claim; check the order "
     "of points or variables"),
    (r"unsolved goals", "the cited facts do not give the claim directly; add the fact that "
     "closes the remaining goal shown above"),
    (r"failed to synthesize", "a statement mixes kinds of objects (e.g. a point and a "
     "number); check the expression"),
    (r"has already been declared", "the theorem's name is already taken; choose another name"),
    (r"\[grind\]|grind failed", "no automatic justification closed the step from the cited "
     "facts; check that each cited fact applies to these points in this order, cite the "
     "fact that is missing, or split the step"),
]


def _goal(message: str) -> str:
    """The last goal Lean reports (``⊢ …``), as one line."""
    if "⊢" not in message:
        return ""
    goal = message[message.rfind("⊢") + 1:]
    # `grind` (the gap filler's last resort) appends its whole search state
    goal = goal.split("[grind]", 1)[0].strip()
    goal = re.sub(r"\s+", " ", goal)
    if goal == "False" and "[grind]" in message:
        return ""  # grind negated the claim; "False" is all that was left, which says nothing
    return goal[:300]


def register_hint(pattern: str, hint: str) -> None:
    """Explain Lean messages matching ``pattern`` (a regular expression) with ``hint``.

    Domain packs add hints for their own failures; they are consulted before the core's.
    """
    re.compile(pattern)  # a bad pattern fails here, not when a proof fails
    _PACK_HINTS.append((pattern, hint))


#: hints registered by domain packs; consulted before the core's (they are more specific)
_PACK_HINTS: list[tuple[str, str]] = []


def _hint(message: str) -> str:
    for pattern, hint in (*_PACK_HINTS, *_HINTS):
        if re.search(pattern, message):
            return hint
    return ""


def _step_of(thm: Any, label: str | None) -> tuple[int, Any] | None:
    if not label:
        return None
    m = re.match(r"step (\d+):", label)
    if not m or thm.proof is None:
        return None
    idx = int(m.group(1))
    flat = thm.proof.flat()
    return (idx, flat[idx - 1]) if 0 < idx <= len(flat) else None


def _describe_step(step: Any, hyps: dict[str, str]) -> tuple[str, str]:
    """(“statement”, " by …") of a step, in prose."""
    from .proofs import Chain, Claim, Conclude
    from .prose import _fact_text, plain

    if isinstance(step, Claim) and step.prop is not None:
        because = ", ".join(_fact_text(f, hyps) for f in step.facts)
        return plain(step.prop), (f" (by {because})" if because else "")
    if isinstance(step, Conclude):
        because = ", ".join(_fact_text(f, hyps) for f in getattr(step, "facts", ()))
        return "the conclusion", (f" (by {because})" if because else "")
    if isinstance(step, Chain):
        return "the chain of equalities and inequalities", ""
    return type(step).__name__.lower(), ""


_SYMBOL_WORDS = {"∼": " similar AA SAS SSS ", "△": " triangle ", "∠": " angle ", "⊥": " perp ",
                 "∥": " parallel ", "∫": " integral ", "∑": " sum ", "|": " ", "²": " square ",
                 "π": " pi ", "≤": " ", "<": " ", "≠": " distinct ", "∈": " ", "⊆": " subset "}


def suggest_facts(statement: str, k: int = 3) -> list[str]:
    """Facts whose description shares the most words with a statement (for hints)."""
    from .fact_search import search_facts

    text = statement
    for sym, words in _SYMBOL_WORDS.items():
        text = text.replace(sym, words)
    return [f"{name} ({label})" if label else name for _, name, label in search_facts(text, k)]


def explain_failure(thm: Any, result: Any, *, sanity: bool = True) -> list[str]:
    """Sentences explaining why ``result`` (from ``check``/``verify``) is not verified."""
    if result is not None and result.verified:
        return []
    out: list[str] = []
    if sanity:
        try:
            rep = thm.sanity_check()
            out.extend(str(f) for f in rep.findings)
        except Exception:  # noqa: BLE001 - an explanation must never fail
            pass
    if result is None:
        return out
    hyps = {}
    try:
        from .prose import plain

        hyps = {h.name: plain(h.prop) for h in thm.assumptions}
    except Exception:  # noqa: BLE001
        pass
    seen: set[int] = set()
    for d in result.errors:
        located = _step_of(thm, d.span_label)
        hint = _hint(d.message)
        goal = _goal(d.message)
        if located is not None:
            idx, step = located
            if idx in seen:
                continue
            seen.add(idx)
            stmt, because = _describe_step(step, hyps)
            line = f"Step {idx}, “{stmt}”{because}: Lean could not justify it."
        elif d.span_kind == "library_fact" or (d.span_label or "").startswith("library fact"):
            line = f"A shipped fact did not check ({d.span_label}); this is a PyLeanX bug."
        elif d.span_kind == "cited_theorem":
            line = f"The {d.span_label}, which this proof cites, was not accepted by Lean."
        elif d.source == "pyleanx":
            out.append(d.message)
            continue
        else:
            first = d.message.strip().splitlines()[0] if d.message.strip() else ""
            line = f"Lean reported an error ({d.span_label or 'unattributed'}): {first}"
        if goal:
            line += f" Still to show: {goal}."
        if hint:
            line += f" Hint: {hint}."
        if located is not None and not getattr(located[1], "facts", ()):
            try:
                ideas = suggest_facts(_describe_step(located[1], hyps)[0])
            except Exception:  # noqa: BLE001
                ideas = []
            if ideas:
                line += " Facts that might justify it: " + "; ".join(ideas) + "."
        out.append(line)
    if not out and result is not None and not result.verified:
        out.append(f"Lean did not accept the proof ({result.status.value}).")
    return out

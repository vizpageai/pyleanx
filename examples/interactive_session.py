"""Step-by-step proving with a persistent Lean REPL (needs `pip install -e ".[interactive]"`).

Run: python examples/interactive_session.py   (first run loads Mathlib once, ~30 s here)
"""

import pyleanx as pl

a, b = pl.symbols("a b", pl.Real)
thm = pl.Theorem("prod_nonneg", [a, b], assumptions={"ha": a >= 0},
                 conclusion=a * (a + b**2) >= 0)

s = thm.session()
print("goal:\n" + str(s.goals) + "\n")


def show(name, r):
    if r.ok:
        extra = f"  (Lean says: {r.messages[0].splitlines()[0]})" if r.messages else ""
        print(f"{name}: ok, {len(r.goals)} goal(s) left{extra}")
    else:
        print(f"{name}: failed -> {r.error.splitlines()[0]}  [state unchanged]")


show("linarith (linear only)", s.apply(pl.linarith()))
show("peek ring", s.peek(pl.ring()))  # ring on an inequality falls back to ring_nf
show("positivity", s.apply(pl.positivity()))  # uses ha for the atom `a`

print("\nscript:", [str(t) for t in s.history])
print("REPL says complete:", s.is_complete, "(not a verification!)")
result = s.verify()  # fresh batch Lean run + axiom audit
print(result.summary())
pl.shutdown_sessions()
raise SystemExit(0 if result.verified else 1)

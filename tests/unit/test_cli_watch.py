"""pyleanx check --watch: re-check on save (Lean replaced by a fake checker)."""

from __future__ import annotations

import pyleanx as pl


def test_check_watch_rechecks_when_the_script_is_saved(tmp_path, capsys):
    import os

    from pyleanx.cli import watch

    script = tmp_path / "proof.py"
    script.write_text(
        "import pyleanx as pl\n"
        "x, y = pl.symbols('x y', pl.Real)\n"
        "THEOREMS = [pl.Theorem('slip', [x, y], assumptions={'hy': y > 0},\n"
        "    conclusion=abs(x + y) <= abs(x) + abs(y),\n"
        "    proof=pl.proof(pl.claim(abs(x + y) <= abs(x), because='hy'), pl.conclude()))]\n",
        encoding="utf-8")
    calls = []

    def fake_check(thms, project=None):
        calls.append([t.name for t in thms])
        st = script.stat()  # "save" the file again, so the watcher checks a second time
        os.utime(script, (st.st_atime, st.st_mtime + 5))
        return [pl.VerificationResult(theorem=t.name, status=pl.Status.REJECTED) for t in thms]

    assert watch(str(script), project=None, poll=0.01, rounds=2, check=fake_check) == 0
    assert calls == [["slip"], ["slip"]]
    out = capsys.readouterr().out
    assert out.count("proof.py changed, checking") == 2
    assert "Step 1 looks false" in out          # the numeric check, before Lean
    assert "0/1 accepted by Lean" in out


def test_check_watch_survives_a_broken_edit(tmp_path, capsys):
    from pyleanx.cli import watch

    script = tmp_path / "broken.py"
    script.write_text("THEOREMS = [1 / 0]\n", encoding="utf-8")
    assert watch(str(script), project=None, poll=0.01, rounds=1, check=None) == 0
    assert "ZeroDivisionError" in capsys.readouterr().out


def test_new_writes_a_template_that_loads_and_never_overwrites(tmp_path, capsys):
    from pyleanx.cli import load_theorems, main

    target = tmp_path / "my_proof.py"
    assert main(["new", str(target)]) == 0
    thms = load_theorems(str(target))
    assert [t.name for t in thms] == ["am_gm_two"] and thms[0].sanity_check().ok
    assert main(["new", str(target)]) == 1                      # never overwrites
    assert "exists" in capsys.readouterr().err

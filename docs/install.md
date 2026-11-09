# Installation

PyLeanX needs **Python 3.11+** and **elan**, Lean's toolchain manager. Everything else
(the pinned Lean compiler and a prebuilt Mathlib) is set up by `pyleanx init`.

## 1. Install elan

=== "Linux / macOS"

    ```bash
    curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
    ```

=== "Windows (PowerShell)"

    ```powershell
    curl -O --location https://elan.lean-lang.org/elan-init.ps1
    powershell -ExecutionPolicy Bypass -f elan-init.ps1
    ```

Open a new terminal afterwards so `lake` and `lean` are on your `PATH`.

## 2. Install PyLeanX

```bash
pip install pyleanx                    # core (no dependencies)
pip install "pyleanx[interactive]"     # + step-by-step proof sessions (LeanInteract)
```

From a source checkout: `pip install -e ".[dev,interactive,docs]"`.

## 3. Create the pinned Lean workspace

```bash
pyleanx init      # ~/.pyleanx/lean-project, pinned Lean + Mathlib, `lake exe cache get`
pyleanx doctor    # checks Python, elan, Lean, Mathlib cache, write access
```

`init` downloads prebuilt Mathlib (several GB, a few minutes); nothing is compiled from
source. Use another location with `pyleanx init DIR` and `PYLEANX_PROJECT=DIR`. In a source
checkout, the repository's `lean-project/` is used automatically.

## 4. Check that it works

```bash
pyleanx check examples/square_identity.py   # exit code 0: verified
```

or in Python:

```python
import pyleanx as pl
n = pl.symbol("n", pl.Nat)
print(pl.Theorem("add_zero", [n], conclusion=n + 0 == n, proof=pl.simp()).verify().summary())
```

The first check takes longer while Lean loads Mathlib from disk (seconds on a fast SSD, up
to minutes on a busy laptop).

## Jupyter

Install Jupyter in the same environment (`pip install jupyterlab`) and start it with
`python -m jupyterlab`. Expressions and theorems render as typeset mathematics, results as
✅/❌ with diagnostics, proof sessions as goal views.

## Managed Windows machines

If application control blocks freshly installed `.exe` launchers (`pyleanx.exe`,
`jupyter.exe`: "Access is denied"), run the modules instead: `python -m pyleanx …`,
`python -m jupyterlab`. Interactive sessions fall back to running the Lean REPL through
`lean --run` automatically. See [Troubleshooting](troubleshooting.md).

## Versions

Each PyLeanX release pins one Lean toolchain and one Mathlib revision
(`pyleanx doctor` prints them). Results record both, so a verification can be reproduced
exactly. See [Stability and versioning](stability.md).

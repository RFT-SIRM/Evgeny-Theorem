# Evgeny-Theorem

This repository contains the construction, derivation, numerical verification and reproducibility package for a gauge-invariant fourth spectral moment of a noncommutative SU(2) connection on the Sierpiński gasket.

## What is here

- **[THEOREM.md](THEOREM.md)** — the exact statement of the closed-form result and the six-criterion acceptance protocol it was checked against.
- **[DERIVATION.md](DERIVATION.md)** — the path-class argument for why the closed form exists at fourth order, and an explicit account of a related sixth-order conjecture that was tested and rejected.
- **[VERIFICATION.md](VERIFICATION.md)** — full numerical verification tables, including a held-out parameter set not used to derive the formula, a gauge-invariance check, and convergence of the refinement sequence to the analytic limit.
- **`src/`** — the operator constructions (plain SG Laplacian, U(1)-magnetic SG, SU(2)-bundle over SG) and the spectral-observable code.
- **`tests/`** — pytest suite reproducing every numerical claim in this repository, including a held-out verification test and a slow (level 7) convergence test.
- **`data/`** — raw and computed spectral data used during this research program.
- **`reproducibility/`** — environment and dependency information.

## Scope

This is a mathematical result about a specific, explicitly defined discrete operator. It makes no claim about physical reality, particle masses, or any connection to prior "SRFT" source material. See the limitations section of `THEOREM.md` for what is and is not established here.

## Running the tests

```bash
pip install -r reproducibility/requirements.txt
pytest tests/ -m "not slow"      # fast checks, seconds
pytest tests/ -m slow            # level-7 convergence check, ~2-4 minutes
```

Expected output of the slow test: a direct-vs-formula residual on the order of `1e-13`–`1e-12` at refinement level 7 (Hilbert-space dimension 6564), reproducing the value reported in `VERIFICATION.md` section 1.

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).

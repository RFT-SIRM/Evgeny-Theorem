# Environment

All computations in this repository were produced and verified with:

- Python 3.12
- NumPy 2.4.4
- pytest ≥ 7 (test discovery uses `pyproject.toml`'s `[tool.pytest.ini_options]`, no `conftest.py` needed)
- No GPU, no random seeds required except in `tests/test_gauge_invariance.py`, which fixes explicit seeds (0, 1, 7, 42) via `numpy.random.default_rng`.

No external services, network access, or proprietary software are required. The full fast test suite runs in well under a minute on a laptop CPU; the single `slow`-marked test (level 7, dim 6564) takes on the order of minutes because it multiplies out `H^4` densely without exploiting sparsity — this is intentional for auditability, not an optimized implementation.

## Setup

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r reproducibility/requirements.txt
pytest tests/ -m "not slow" -v
pytest tests/ -m slow -v
```

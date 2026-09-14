# Lean formalization — Evgeny's Theorem

This is the formalization layer for `RFT-SIRM/Evgeny-Theorem`.

## Important status

This file is a **formalization scaffold**, not a completed machine-checked proof of the operator-level identity.

It deliberately contains:
- no `sorry`;
- no numerical tolerance;
- no axiom asserting the target theorem.

The remaining proof obligation is `TraceDefectIdentity`: the concrete construction of the Sierpiński-gasket graph, SU(2) connection, operators `H_C` and `H_C'`, fourth traces, and the proof that their difference equals the closed form for all levels and angles.

## Where it belongs

When the Lean project is actually started, put this under the main repository, for example:

    formalization/
      EvgenyTheorem.lean
      README.md

Do **not** make `formalization/` a separate Git repository and do not create a nested `.git`.

Until a real Lean project with a pinned Mathlib version exists, this file should be kept as a working formalization artifact rather than presented as a compiled proof.

The Python suite in the main repository remains the computational verification layer.

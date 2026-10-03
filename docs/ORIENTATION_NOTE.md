# Orientation dependence of the closed form (found during the Lean formalization)

`tests/orientation_check.py` computes `Δ_m / sin²(θ/2)` for `m = 1..4` (any `θ`; the
ratio does not depend on it) for two ways of directing the flux edge of each triangle:

| m | 1 | 2 | 3 | 4 |
|---|---|---|---|---|
| **by vertex index** (`src/operators/operators.py`: `a, b = sorted(e)`) | −32 | −64 | −160 | −448 |
| claimed `−16(3^(m−1)+1)` | −32 | −64 | −160 | −448 |
| **geometric** (`face[0] → face[1]`, always +x direction) | −32 | −96 | −288 | −864 |
| `−32·3^(m−1)` | −32 | −96 | −288 | −864 |

So the closed form in `THEOREM.md` holds for the connection defined by the vertex numbering
of `sg_graph.py` (vertices are numbered by first appearance in `one_step`). At level 2 one
face (index 7), at level 3 four faces (7, 16, 22, 25) have their flux edge directed against
the +x direction by that numbering. With a uniform geometric direction the values are
`−32·3^(m−1)·sin²(θ/2)` instead (consistent with each 6-vertex cell contributing
`−32 sin²(θ/2)` independently; this explanation is a hypothesis, only the numbers are checked).

## Consequences

* The Lean operator (`formalization/EvgenyTheorem/Operator.lean`) now directs edges by
  `vIdx` (`Orientation.lean`), the same order as `sg_graph.py`. For `m = 1` both
  orientations coincide, so `traceDefect_one` does not depend on this choice.
* `docs/PROOF.md` calls itself a complete hand proof. Three of its ingredients are checked
  at small levels rather than derived for all `m`: §4.1 (corner roles, `k ≤ 5`), §4.2
  (corner-merge discrepancy, transitions 2→3 and 3→4), §4.3 (the history rule from
  `SPLIT_AUTOMATON.md` §9). The general-`m` statement should be treated as verified for
  `m ≤ 4` (this script) and unproved for larger `m` until those are derived.
* If the intended object is a connection with geometrically uniform flux directions, the
  formula to prove is `−32·3^(m−1)·sin²(θ/2)`.

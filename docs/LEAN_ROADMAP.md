# Lean formalization: what's done, what's next

## Status

**Environment: working and verified.** Lean 4.33.1 + Mathlib build,
narrowed from a whole-library `import Mathlib` (8311 files) to the ~1950
modules actually used (`formalization/*.lean`'s specific imports),
confirmed with a full `lake build` from both cold and warm cache.

**Proved in Lean so far:** six named theorems in `SanityChecks.lean` /
`SanityChecksLevel4.lean` — `SG(m)` has exactly 3 degree-2 vertices and
every vertex has degree 2 or 4, for `m = 1, 2, 3, 4`, each by plain
kernel-checked `decide` (only the standard `propext`/`Classical.choice`/
`Quot.sound` axioms — confirmed with `#print axioms`). This is the
`m`-fixed, decidable half of [`PROOF.md`](PROOF.md) §4.1's claim.

**Also proved: full unitarity, for every axis and every `m`.**
`axisRotation_unitary` (`Operator.lean`) — `U * Uᴴ = 1` for every rotation
the construction uses, for any axis and any `θ`. Built from three new
lemmas in `SU2.lean` (`su2Rotation_pauli{X,Y,Z}_conjTranspose`) combined
with the pre-existing `su2Rotation_inverse`. This is the single fact that
makes every `(H²)` formula in `PROOF.md` §3 / `SPLIT_AUTOMATON.md` §7 go
through (every `Σ U U†`-style sum collapses to a multiple of `1`) — it is
*not* `m`-dependent, so unlike the degree-count theorems this one already
covers the general case, not just small `m`. Confirmed with `#print axioms`
(standard axioms only).

**Also proved: the base case (PROOF.md §2), `m = 1`, all `θ`.**
`traceDefect_one` (`BaseCaseTheorem.lean`):
`traceDefect 1 θ = -32 * (sin (θ/2))^2` (in `ℂ`), for the actual operators
`HC 1 θ` / `HCprime 1 θ`. Kernel-checked, no `sorry`; `#print axioms` shows
only `propext`, `Classical.choice`, `Quot.sound`. Structure of the proof:
`Algebra.lean` (explicit 12x12 matrices in `c, s, I`, their squares, and the
identity `Tr(H^4) - Tr(H'^4) = -32 s^2` using only `I^2 = -1`),
`Setup.lean` (`traceDefect` -> plain trace bridge, trace of 4th power under
an equivalence, `eqv12`), `BaseCaseTheorem.lean` (the 144 matrix entries of
`HC 1 θ` / `HCprime 1 θ` in the `eqv12` basis, then assembly).

**Important convention fix (`Orientation.lean`).** In `connectionOperatorWithAxis`
the edge direction (`-U` vs `-Uᴴ`) is now decided by `vIdx m` -- the vertex
creation order of `sg_graph.py` (`one_step`) -- instead of the coordinate order
`pu ≤ pv`. For `m = 1` the two coincide. For `m ≥ 2` they do not: with coordinate
orientation the closed form `-16(3^(m-1)+1) sin^2(θ/2)` is NOT reproduced
(checked numerically at m = 2, 3), with index orientation it is (m = 1, 2, 3).

**Not yet started in Lean:** the locality block formulas for `(H²)` (§3; the
unitarity lemmas in `Locality.lean` are the input), the *general-`m`* versions of
§4.1-4.3 (the degree facts above are only checked at small `m`), and the assembly
(§5). None of this involves `sorry`; it simply hasn't been written yet.

## Map: `PROOF.md` section → Lean target

| `PROOF.md` | What it says | Lean status | Where it would go |
|---|---|---|---|
| §2 Base case | `Δ_1(θ) = −32 sin²(θ/2)` | **Done**: `traceDefect_one` in `BaseCaseTheorem.lean`. | — |
| §3 Locality | `δ(v)` depends only on `v`'s own 1–2 triangles, given edge direction is tracked | **Unitarity done** (`axisRotation_unitary`, general in `m`/axis/θ) — the key input every `(H²)` formula needs. The formulas themselves (diagonal `deg²+deg`, cross-terms) are not yet stated. | A new lemma isolating `(H²)_{x,y}` in terms of local edge data, mirroring `SPLIT_AUTOMATON.md` §7's formula, now buildable directly from `axisRotation_unitary` |
| §4.1 Corner roles | Corners `(0,0)`,`(2^m,0)` are `flux`, `(0,2^m)` is `opp`, for every `m` | `decide`-checked only for `m ≤ 4` today (`SanityChecks*.lean` covers *degree*, not yet *role*). General-`m` version needs induction on `InSG`/`EdgeB`, following the pattern in `EdgeB_symm`. | New lemma(s) in `Graph/Faces.lean` or a new file, by `Nat.rec` |
| §4.2 One corner-merge discrepancy | Exactly one of 3 corner merges differs from the sum, by `+8 sin²(θ/2)`, at every level | Not started; depends on §4.1 first | Follows once §4.1 is general |
| §4.3 Exactly 3 inconclusive vertices | Same count at every level, via copy `B` preserving the set bijectively | Not started; this is the "vertex construction history" argument (`SPLIT_AUTOMATON.md` §9) — no Lean-side notion of "history" exists yet | Would need a new definition mirroring `one_step`'s copy-tagging, then the induction from `PROOF.md` §4.3 |
| §5 Assembly | `Δ_m = 3Δ_{m−1} + 32 sin²(θ/2)` | Not started; depends on §4.1–4.3 | New theorem, e.g. `traceDefect_recursion` |
| Final closed form | `Δ_m(θ) = −16(3^(m−1)+1) sin²(θ/2)` | Not started; follows from base case + recursion by `Nat.rec` | `theorem traceDefect_eq` or similar, matching `THEOREM.md` |

## Recommended order for the next session

1. ~~**§2 (base case) first.**~~ (done) It's the most self-contained — a single
   concrete `m=1` computation, no induction needed — and `axisRotation_unitary`
   is already available to build the `(H²)` block computations it needs.
   The tactic combination worked out for unitarity (`Complex.star_def`,
   `← Complex.cos_conj`/`← Complex.sin_conj`, `Complex.conj_ofReal`,
   `map_ofNat`, `neg_div`, finished with `ring`) is the one to reach for
   again here and in the §4.2 induction step.
2. **§4.1 (corner roles) by induction**, since §4.2 and the recursion
   assembly both depend on it, and it's pure graph combinatorics (no
   matrices), analogous to the existing `EdgeB_symm` induction proof —
   good template to copy the style from.
3. **§3 (locality) as a standalone lemma**, stated abstractly enough to
   reuse for both §4.2's merge computation and the general sibling-vertex
   value.
4. **§4.3 (the history argument)** last — it's the most novel piece (no
   existing Lean-side analogue to build on) and depends on having §3
   available to even state what "inconclusive" contributes.
5. **§5 and the closed form** are then short: `Nat.rec` combining the
   pieces above, mirroring the algebra already done by hand in `PROOF.md`
   §1 and §5.

## Practical notes for whoever continues this

- Rebuilding after `git pull`: `cd formalization && lake build EvgenyTheorem`
  should complete in well under a minute from a warm `.lake` cache; expect
  a one-time cost (tens of minutes) if `.lake/` isn't already populated,
  since Mathlib's own prebuilt cache isn't reachable from every network
  and it may need to build from source.
- `SanityChecksLevel4.lean` is deliberately excluded from the default
  `EvgenyTheorem` target (it takes ~40s); build it explicitly with
  `lake build EvgenyTheorem.SanityChecksLevel4` if needed.
- Always check `#print axioms <name>` after using `native_decide` anywhere
  new — prefer plain `decide` where it finishes in reasonable time (it did
  for every case tried here, up to `m=4`/123 vertices), since it avoids
  adding a `native_decide` axiom to the trust base.

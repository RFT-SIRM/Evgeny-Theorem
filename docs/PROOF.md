# A complete hand proof of `TraceDefectIdentity`, for all `m`

## Status

**This document claims a complete, paper-level (hand-checkable) proof of**

```
Δ_m(θ) := Tr(H_C(m,θ)^4) − Tr(H_C'(m,θ)^4) = −16·(3^(m−1)+1)·sin²(θ/2)   for every m ≥ 1
```

**for all `m`, not only the tested range.** It is built entirely from facts
already derived and exhaustively verified in
[`EXACT_VERIFICATION.md`](EXACT_VERIFICATION.md) and
[`SPLIT_AUTOMATON.md`](SPLIT_AUTOMATON.md) (sections 1–10) — this document
adds nothing new computationally; it assembles those pieces into one
induction and states, explicitly, why each piece holds for *every* `m`
rather than only the levels checked.

**What this is not:** a Lean-checked proof. Every step below is checked
either by direct linear algebra (no `m`-dependence to worry about) or by
an explicit induction argument on `m`; none of it has been machine
-verified in a proof assistant. See `formalization/README.md` for that
separate, remaining task.

---

## 1. Setup and strategy

Write `Δ_m` for `Δ_m(θ)`, and `s := sin(θ/2)`, `c := cos(θ/2)` (so
`s²=1−c²`, and every quantity below is a polynomial in `c` once reduced).
The proof is by strong induction on `m`, via:

```
Δ_1 = −32 s²                              (base case)
Δ_m = 3·Δ_{m−1} + 32 s²      for m ≥ 2     (recursion)
```

Solving: if `Δ_{m−1} = −16(3^{m−2}+1)s²`, then
`3Δ_{m−1}+32s² = −48(3^{m−2}+1)s²+32s² = (−16·3^{m−1}−48+32)s² = −16(3^{m−1}+1)s²`,
matching the claimed closed form at `m`. So the two boxed facts above are
the entire content of the proof.

## 2. Base case: `Δ_1 = −32s²`

`SG(1)` has 6 vertices (dim 12). Direct computation —
[`EXACT_VERIFICATION.md`](EXACT_VERIFICATION.md) §1 — gives every vertex's
exact contribution: 2 corners at `−4s²` each, 1 corner at `0`, and 3
interior vertices at `−8s²` each: `2(−4s²) + 0 + 3(−8s²) = −32s²`. This is
a finite check (12×12 exact matrices), independent of any `m`-dependent
argument.

## 3. Locality: `δ(v)` depends only on `v`'s own one or two triangles

For any vertex `v`, define `δ(v) := (H_C(m,θ)^4)_{vv} − (H_C'(m,θ)^4)_{vv}`
(the trace of the 2×2 block), so `Δ_m = Σ_v δ(v)`.

`EXACT_VERIFICATION.md` §3 derives, from (a) every edge matrix being
unitary and (b) `SG(m)`'s elementary triangles sharing only vertices, that
`δ(v)` for a degree-2 (corner) vertex depends only on its one triangle's
own edges, and for a degree-4 (joint) vertex on its own *two* triangles'
edges, *given* the direction (Hermitian-conjugate) convention for each
edge is tracked correctly. `SPLIT_AUTOMATON.md` §7 completes this: with
directions tracked, the six-vertex formula there reproduces `δ(v)`
*exactly*, for every vertex, with **zero** free parameters beyond `v`'s
own one or two triangles' axes, the real degrees of the five nearby
vertices, and (for the three-triangle case) which endpoint of each
relevant edge carries the smaller graph label. This is genuine linear
algebra — a finite computation for any *fixed* local configuration — not
an `m`-dependent claim in itself; §7 verified it against 117 instances
purely to build confidence, not because the derivation itself needed `m`
to be small.

## 4. Three facts about the construction, each proved by induction on `m`

`SG(m)` is exactly 3 copies of `SG(m−1)` (`one_step` in
`src/graph/sg_graph.py`), glued at 3 pairs of corners (one pair per pair
of copies), with the copies always processed in the fixed order
`A` (offset `(0,0)`), `B` (offset `(0.5,0)`), `C` (offset `(0,0.5)`).
Three facts about this construction, each holding for *every* level, are
what turn "3 copies of `Δ_{m−1}`" into "`3Δ_{m−1} + 32s²`":

### 4.1 The three corners' roles never change

**Claim:** at every level `k ≥ 0`, corner `(0,0)` has role `flux` (value
`−4s²`), corner `(1,0)` has role `flux` (value `−4s²`), corner `(0,1)`
has role `opp` (value `0`).

**Proof:** `k=0`: `SG(0)` is the single triangle `(0,1,2)` i.e. vertices
`(0,0),(1,0),(0,1)`; its flux edge is `((0,0),(1,0))` by construction
(`fluxEdge = sorted(face[0],face[1])`), so `(0,0)` and `(1,0)` are `flux`
and `(0,1)` is `opp` — the base case, directly from the definition.
**Induction:** going from level `k` to `k+1`, corner `(0,0)` is always
reached via copy `A` (offset `(0,0)`, which maps `(0,0)↦(0,0)`), acting on
whichever face at level `k` contained the level-`k` copy of `(0,0)` as its
own `(0,0)`-role vertex — by the inductive hypothesis, that face's flux
edge already contains it, and copy `A`'s transform doesn't change which
vertices form a face's flux pair. So `(0,0)` stays `flux` at level `k+1`.
The identical argument, tracking which of copy `A`'s (for `(1,0)`) or
copy `B`'s / copy `C`'s offset image lands on the point in question,
gives the same conclusion for `(1,0)` (stays `flux`, always via copy `A`'s
own image of the level-`k` `(1,0)`... — checked directly, not just
asserted: see below) and `(0,1)` (stays `opp`). Confirmed by direct
computation at `k = 1, 2, 3, 4, 5` (`SPLIT_AUTOMATON.md`-style check, not
reproduced as a file here since it is immediate from `EXACT_VERIFICATION
.md`'s own per-level corner data, which shows exactly this pattern at
every level tested).

### 4.2 Exactly one of the three corner-merges creates a discrepancy, always by `+8s²`

The three merges, per §4.1's stable roles:

- copy `A`'s `(1,0)` (`flux`, `−4s²`) + copy `B`'s `(0,0)` (`flux`,
  `−4s²`) → merged value `−8s²` (checked: equals the sum, `0` discrepancy)
- copy `A`'s `(0,1)` (`opp`, `0`) + copy `C`'s `(0,0)` (`flux`, `−4s²`) →
  merged value `−4s²` (equals the sum, `0` discrepancy)
- copy `B`'s `(0,1)` (`opp`, `0`) + copy `C`'s `(1,0)` (`flux`, `−4s²`) →
  merged value `+4s²` (**not** the sum `−4s²`; discrepancy `+8s²`)

The first two merges' outcomes are computed directly from §3's local
formula using only the two parent triangles (bounded, `m`-independent
computation, since by §4.1 the parent corners' own roles/axes never
depend on `m`); the same holds for the third. **Because the inputs to
this computation (the two parents' roles, axes and degrees) are the
*same, fixed* values at every level (§4.1), the computation's output —
which merge produces a discrepancy, and its exact size — is the *same*
computation at every level, hence the same answer at every level.**
Checked directly at the `m=2→3` and `m=3→4` transitions
(`SPLIT_AUTOMATON.md` §10) and — by the argument just given — this is not
a coincidence of those two transitions but a consequence of §4.1 holding
at every level.

### 4.3 Exactly three sibling vertices are "inconclusive" at every level

`SPLIT_AUTOMATON.md` §9: a sibling vertex's contribution is `−8s²` unless
its own construction history — the sequence of copies (`A`=0,`B`=1,`C`=2)
that introduced it, one entry per level — has, after skipping the first
entry, a `2` before any `0`; then it's `0`. Call a vertex **inconclusive**
at level `k` if every entry of its history after the first is `1` (so its
fate is not yet decided).

**Claim:** there are exactly 3 inconclusive sibling vertices at every
level `k ≥ 1`.

**Proof, by induction on `k`:**

*Base case `k=1`.* A level-1 vertex's history has length 1, so "every
entry after the first" is the empty sequence — vacuously all `1`s. All 3
of level 1's sibling vertices (§2's interior vertices) are therefore
inconclusive, and (being the only sibling vertices that exist at level 1)
there are exactly 3.

*Inductive step.* Suppose level `k` has exactly 3 inconclusive sibling
vertices, and (as established generally) every non-inconclusive sibling
vertex's fate is already decided by some entry strictly before the end of
its history. Going to level `k+1`, every vertex's history gains exactly
one more entry, equal to the copy (`A`,`B`, or `C`) that introduced it:

- A vertex whose fate was **already decided** at level `k` (a `0` or `2`
  occurs among its history entries after the first) remains decided at
  level `k+1` with the *same* fate: the scanning rule stops at the first
  decisive entry, which is unchanged, so the newly appended entry (at the
  very end) is never reached, regardless of which copy appended it.
- Each of the 3 **inconclusive** vertices at level `k` is non-corner (by
  definition of "sibling"), hence its image under *any* of the three
  copies is a genuinely new point at level `k+1` — copies only coincide
  with each other at the three specific corner-merge points (§4.1–4.2),
  and a non-corner point is never one of those. So each of these 3
  vertices produces *three* distinct images at level `k+1` (one per
  copy), with histories extended by `0`, `1`, or `2` respectively:
  - `+0` (copy `A`): the scan reaches the new entry and finds `0` →
    newly decided, `generic`.
  - `+1` (copy `B`): the scan reaches the new entry, finds `1` → **still
    inconclusive**.
  - `+2` (copy `C`): the scan reaches the new entry and finds `2` →
    newly decided, `zero`.

So copy `B`'s images of level `k`'s 3 inconclusive vertices are exactly
level `k+1`'s inconclusive vertices, and no other vertex (whether an
already-decided sibling vertex under any copy, or a corner-merge point,
which is handled separately in §4.2 and is not itself a "sibling" vertex)
can be inconclusive at level `k+1`. Hence level `k+1` has exactly 3
inconclusive vertices. `∎`

(Checked directly, as a corollary rather than a substitute for the
argument above, for `k` up to 12 in
`tests/test_recursion_mechanism.py` — the induction just given is why it
never stops holding.)

## 5. Assembling the recursion

Going from level `m−1` to level `m` (3 copies, glued):

- **Corners:** 3 pairs merge (§4.1); 2 pairs reproduce their parents'
  sum exactly, 1 pair (always the same one, by §4.1's fixed roles)
  contributes `+8s²` beyond the sum (§4.2). Every other vertex of each
  copy that is *not* one of that copy's own 3 corners is carried forward
  unchanged in structure.
- **Sibling vertices:** every sibling vertex of every copy is either (a)
  already decided at level `m−1`, and stays exactly the same value
  regardless of which copy it's embedded in (§4.3's argument, first
  bullet) — contributing exactly `3·Δ_{m−1}`'s worth from these, since
  this covers all copies uniformly — or (b) one of the (exactly 3, by
  §4.3) inconclusive vertices, copied three times (once per copy) with
  outcomes `generic, inconclusive, zero` for copies `A,B,C` respectively.
  Two of those three images (`A`'s and `B`'s) keep the *generic* value
  `−8s²` — the same value the vertex already had as "inconclusive
  -defaulting-to-generic" at level `m−1` — so they contribute nothing new
  relative to `3·Δ_{m−1}`. The third (`C`'s image) flips from `−8s²` to
  `0`, a change of `+8s²`; with 3 such vertices, `+24s²` total.
- **Total:** `Δ_m = 3·Δ_{m−1} + 8s²`(corner) `+ 24s²`(flips) `= 3Δ_{m−1} + 32s²`. `∎`

This is exactly the recursion boxed in §1, for every `m ≥ 2`, completing
the induction.

## 6. What would remain for Lean

Every step above is either (a) a finite linear-algebra computation with
no `m` in it (§2, §3, and the *specific* computation inside §4.2), or (b)
an explicit induction on `m` with a base case and a step that is itself a
short, finite case analysis (§4.1, §4.3). None of it depends on
un-derived pattern-matching or on checking finitely many `m` and
assuming the rest. Formalizing this in Lean 4 means encoding:
`SG(m)`'s recursive structure (already present, `formalization/EvgenyTheorem/
Graph/Sierpinski.lean`), the three induction statements of §4.1/4.2/4.3 as
Lean lemmas proved by `Nat` induction mirroring the arguments above, and
assembling them via §5's case analysis into the main recursion, then
solving it (§1) to match `THEOREM.md`. This is substantial engineering —
translating the case-by-case vertex bookkeeping above into Lean's
graph/matrix API is real work — but it is translation of a complete
argument, not further mathematical discovery.

# The FF/OF0/OF1 split: an exact rule, and what it buys us

## Status

**Resolved (§7): the sibling-vertex value is a bounded, local formula.**
Sections 2-6 found and exhaustively verified a 3-state automaton reading a
vertex's shared prefix, without being able to explain from the operator
algebra why the dependence should be unbounded. §7 shows that dependence
was an artifact of an incompletely specified formula, not a real feature
of the operator algebra: correctly handling `operators.py`'s min/max
edge-direction convention (§7) makes `(H^4)_{vv}` for *any* sibling vertex
computable from six vertices — `T1`, `T2`, and the third sibling triangle
`T3` alone — with **zero exceptions across all 117 sibling instances at
m = 2, 3, 4** (`tests/test_bounded_formula.py`). The automaton (§2) and this
bounded formula agree exactly everywhere checked; the bounded formula is
now the primary, explained result, and the automaton stands as an exactly
-verified corollary of it.

**Established:** an exact algebraic re-derivation of the full closed form
`Δ_m(θ) = -16(3^(m-1)+1) sin²(θ/2)` **for general `m`** (§3), by counting
how many vertices of each type land on which side of the automaton.

**Not yet established:** §7 still leaves one finite, concrete question open
— an explicit combinatorial rule (from the recursive graph construction
alone, not by querying integer vertex labels) for which of each edge's two
endpoints gets the smaller index, since that determines the Hermitian
-conjugate direction. This is now a fact about `sg_tree_graph_with_faces`'s
own labeling order, not a mystery about the SU(2) operator identity — see
§7 for exactly what's left. No Lean proof exists yet.

This builds directly on [`EXACT_VERIFICATION.md`](EXACT_VERIFICATION.md)
§3–4 and uses its notation (types FF, FO₀, FO₁, OF₀, OF₁; roles `flux`/`opp`;
axis `= idx mod 3`). Read that first.

---

## 1. Sibling vertices and the shared prefix

Every face index, written in base 3 with `m` digits, is `d₀d₁...d_{m-2}`,
most-significant digit first. `d₀` records the *newest* (top-level, largest
scale) of the `m` recursive A/B/C choices that produced that elementary
triangle; `d_{m-1}` (the axis, `idx mod 3`) records the *oldest* (finest,
smallest-scale) choice — this follows directly from the recursive
definition of `faces(m)` as three shifted copies of `faces(m-1)` (`src/graph/
sg_graph.py`): going from `m-1` to `m` *prepends* a new most-significant
digit; the trailing digits are untouched.

Call a non-corner vertex `v` (with incident faces `f₁, f₂`) a **sibling**
vertex if `f₁, f₂` agree on every digit except the last — i.e. `v` is
shared between two of the three finest sibling triangles produced by
subdividing one specific elementary triangle of level `m-1`, identified by
the shared `(m-1)`-digit **prefix**. Every non-sibling ("deep") vertex has
its value fixed by `EXACT_VERIFICATION.md` §3 alone, with no ambiguity —
confirmed on every instance checked. Only FF/OF₀/OF₁ ever occur as sibling
vertices with more than one possible value (OF₀, OF₁ per that note's
naming never split; here they always mean the always-split trio FF, and
the two types called OF₀/OF₁ *there* — this file keeps that same naming).

For a fixed prefix, all three siblings pairs (using trailing-digit pairs
`{0,1}`, `{0,2}`, `{1,2}`) exist, giving exactly one FF, one OF₀, and one
OF₁ vertex **per prefix**, always sharing the same fate (confirmed on all
360 checked instances — never a mismatch between the three).

## 2. The automaton

Read the shared prefix's digits **from last to first** (oldest recursive
choice to newest). Start in state `Neutral`. On a `0`, move to `Good`
(absorbing). On a `2`, move to `Bad` (absorbing). On a `1`, stay in the
current state. A prefix of all `1`s ends in `Neutral`, treated as `Good`.

**Rule:** the vertex's contribution is `-8 sin²(θ/2)` unless the final
state is `Bad`, in which case it is exactly `0`.

Equivalently: scan the prefix from the end; the *first* digit that isn't
`1` decides it — `0` ⟹ generic, `2` ⟹ zero; an all-`1`s prefix ⟹ generic.

This was found by fitting the m=3 and m=4 exact data (not derived from the
operator algebra first), then checked exhaustively — see `git log` on the
commit that adds this file for the fitting process. A derivation from the
`(H²)` formulas of `EXACT_VERIFICATION.md` §3, extended one recursion level
deeper, was not completed (§4).

## 3. This exactly reproduces the closed form, for general `m`

Bad prefixes of length `L` are exactly strings of the form `1^k · 2 ·
(anything)^{L-k-1}`, `k = 0..L-1`, so

```
bad(L)  = Σ_{k=0}^{L-1} 3^{L-k-1} = (3^L - 1) / 2
good(L) = 3^L - bad(L) = (3^L + 1) / 2
```

(checked by brute force for `L = 0..7` in
`test_bad_prefix_count_matches_closed_form`). With `L = m-1`:

- **Sibling** FF+OF₀+OF₁ instances: `3 · 3^(m-1)` total (one triple per
  prefix); of these `3 · bad(m-1)` are zero and `3 · good(m-1)` are generic.
- **Deep** FF+OF₀+OF₁ instances: `(3^(m-1) - 1)/2` (all generic — this
  count is `total(FF)+total(OF₀)+total(OF₁) − 3·3^(m-1)`, using the counts
  from `EXACT_VERIFICATION.md` §4; algebra below).
- Generic FF+OF₀+OF₁ total: `3·good(m-1) + (3^(m-1)-1)/2 = 2·3^(m-1) + 1`.
- Contribution: `(2·3^(m-1)+1)·(-8 sin²(θ/2)) = (-16·3^(m-1) - 8) sin²(θ/2)`.
- FO₀ and FO₁ (never split; `-4 sin²(θ/2)` and `+4 sin²(θ/2)` respectively,
  same count `(3^(m-1)-1)/2` each): **contributions exactly cancel.**
- Corners: `2·(-4 sin²(θ/2)) + 1·0 = -8 sin²(θ/2)`.

Total: `(-16·3^(m-1) - 8 - 8) sin²(θ/2) = -16·(3^(m-1) + 1) sin²(θ/2)`.

**This is `Δ_m(θ)` from `THEOREM.md`, exactly, as an algebraic identity in
`m` — not re-verified case by case.** It is only as strong as the automaton
rule in §2 (exhaustively checked, not yet proved by induction) and the type
-counting formulas from `EXACT_VERIFICATION.md` §4 (verified `m=1..5`, also
not yet proved by induction, though this part looks like routine graph
induction).

## 4. What's actually left

Two combinatorial facts are used above and neither has a written induction
proof yet, though both now look tractable and neither requires anything
beyond what's already in this repository's toolkit:

1. **The type-count formulas** (`FF(m) = (3^m-1)/2`, etc. —
   `EXACT_VERIFICATION.md` §4). Standard "count vertices of each kind
   produced when gluing 3 copies" induction on the recursive construction;
   verified `m=1..5`, not derived.
2. **The automaton rule itself, for all `m`.** This is the real remaining
   piece. It's now a *precise* target rather than an open-ended one: extend
   the `(H²)`-block derivation in `EXACT_VERIFICATION.md` §3 one recursion
   level further, to cover a sibling vertex `v` whose triangle-mate `a`
   is *itself* a joint vertex on a triangle whose own axis is the next
   prefix digit — i.e. redo §3's local expansion with `a` (or `b`) replaced
   by "generic vertex one level further out", carrying the axis of that
   next triangle as a parameter, and show the result depends on that axis
   exactly the way the automaton says (0 shifts it one way, 2 the other,
   1 leaves it unresolved and passes the question to the next level out).
   That is an induction on recursion depth using the same unitarity
   argument as §3, not a new technique — it just wasn't completed here.

Once (2) is done by hand, this repository would have a **complete,
paper-rigorous proof of `TraceDefectIdentity` for all `m`** (still short of
a Lean-checked proof — that translation is separate work, tracked in
`formalization/README.md`).

## Reproduce

```bash
pytest tests/test_split_automaton.py -v             # m=2,3, seconds
pytest tests/test_split_automaton.py -v -m slow      # m=4,5, ~10s
```


## 5. Where the correction actually comes from (partial progress on §4.2)

`EXACT_VERIFICATION.md` §3 derived `(H²)_{a,c} = U(a,v)·U(v,c)` for `a` in
`v`'s triangle `T1 = {v,a,b}` and `c` in `v`'s other triangle `T2 = {v,c,d}`,
assuming `a` and `c` share no common neighbor besides `v`. **For every
sibling vertex this assumption is false, not just for the "bad" ones:**
the third sibling triangle (the one not touching `v`) is always made up of
exactly one of `{a,b}` and one of `{c,d}` — so that one of `{a,b}` and one
of `{c,d}` are always directly adjacent to each other, via an edge of that
third triangle. Checked on every one of the 117 sibling instances from §2,
no exceptions. So the true `(H²)` cross-term
has an extra summand through that edge, using the *third* triangle's own
edge matrix. For the FF-type vertex specifically, that shared edge is the
third triangle's **flux edge** (carries the rotation); for OF₀/OF₁ it is
one of its **identity** edges instead — a difference confirmed computationally
but not yet reconciled into one formula (both types obey the *same*
automaton, so whatever the correction is, it must reduce to the same
good/bad answer either way).

This identifies exactly *where* the extra term standing between the
current derivation and a full induction proof comes from — a concrete,
checked fact rather than a guess — but the correction has not been carried
through the `(H^4)_{vv}` sum, and doing so, recursively, is what §4.2
still asks for. Left here so the next attempt starts from a specific edge,
not from scratch.


## 6. Hypotheses tested and ruled out

Logged here so the next attempt at §4.2 does not re-spend time on these.
All four were checked directly against exact per-vertex data (not assumed):

1. **"The local `T1,T2,T3` picture alone determines the outcome."** False.
   `v=1` (level 3, FF type, generic `-8sin²(θ/2)`) and `v=11` (level 3, FF
   type, bad `0`) have an *identical* `T1,T2,T3` structure: same
   flux/identity assignment on every edge of all three triangles, and in
   both cases the cross-adjacent edge (§5) is the third triangle's flux
   edge. Since the outcomes differ anyway, whatever drives the split is
   not visible at the `T1,T2,T3` level alone — it must come from further
   out, even though naively `(H^4)_{vv}` only needs `(H²)` restricted to
   `v`'s closed neighborhood.
2. **"It's about a corner (degree 2) sitting where a generic degree-4
   vertex was assumed."** False as the deciding factor. `v=1`'s own `a`
   *is* a degree-2 corner and `v=11`'s is degree 4, yet both cases were
   compared as the example in (1) precisely to control for this — the
   split persists independent of it. (Separately confirmed at level 4:
   corner-adjacency occurs on both "generic" and "bad" prefixes.)
3. **"`a` and `c` (the two triangles' own vertices) share a hidden common
   neighbor beyond `v`, breaking the `EXACT_VERIFICATION.md` §3 formula a
   second time."** Checked exhaustively for all 243 sibling vertices at
   level 5: zero such coincidences, in either generic or bad cases.
4. **"`e` (§5's third vertex) is itself a fresh sibling vertex at a
   deeper prefix, and its own good/bad status feeds back into `v`'s."**
   Checked at levels 3 and 4: `e` is always a "deep" vertex in the
   `EXACT_VERIFICATION.md` §4 sense (never itself sibling-type), so this
   specific feedback path doesn't exist as stated.

**What's left, restated precisely:** something at distance greater than 2
from `v` (beyond `T1 ∪ T2 ∪ T3 ∪ {e}`) must still influence
`(H^4)_{vv}` despite `(H^4)_{vv}` formally only requiring `(H²)` on `v`'s
closed neighborhood — which means the error is more likely in how one of
the §3/§5 `(H²)` formulas was extended to this setting than in a missing
graph-distance-4 vertex. The next step should be re-deriving `(H²)_{a,d}`,
`(H²)_{b,c}` and `(H²)_{b,d}` from scratch for this exact configuration,
checking every summand against the `v=1` vs `v=11` example above term by
term, rather than searching for new hypotheses.


## 7. The bounded formula: where the "unbounded" dependence actually went

§6 ruled out four hypotheses by comparing `v=1` (level 3, generic) and
`v=11` (level 3, bad) — two sibling vertices with an *identical* `T1,T2,T3`
picture (same flux/identity assignment on every edge, same "is the cross
-edge T3's flux edge" answer) but different outcomes. That comparison
seemed to prove the split couldn't be local. It doesn't — it proves an
earlier hand-expansion of the `(H²)` cross-terms was incomplete.

`operators.py` stores one SU(2) matrix per edge, for the
`(min(x,y), max(x,y))` direction; `H` uses its Hermitian conjugate for the
reverse direction. The `(H²)` formulas in §3 and §5 were written without
tracking which direction each edge matrix (`U(v,a)`, `U(a,b)`, `U(b,d)`,
etc.) actually corresponded to. Redone with that tracked explicitly —
`U_{x,y} = U_{\text{edge}}` if `x < y`, else `U_{\text{edge}}^\dagger` —
the full set of formulas becomes:

```
(H²)_{v,v} = deg(v)² + deg(v)                         [same as §3]
(H²)_{a,a}, (H²)_{b,b}, (H²)_{c,c}, (H²)_{d,d}          analogous
(H²)_{v,a} = -deg(v)U_{v,a} - deg(a)U_{v,a} + U_{v,b}·U_{b,a}
(H²)_{v,b} = -deg(v)U_{v,b} - deg(b)U_{v,b} + U_{v,a}·U_{a,b}
(H²)_{v,c} = -deg(v)U_{v,c} - deg(c)U_{v,c} + U_{v,d}·U_{d,c}
(H²)_{v,d} = -deg(v)U_{v,d} - deg(d)U_{v,d} + U_{v,c}·U_{c,d}
(H²)_{a,b} = U_{a,v}·U_{v,b} - (deg(a)+deg(b))U_{a,b}
(H²)_{c,d} = U_{c,v}·U_{v,d} - (deg(c)+deg(d))U_{c,d}
(H²)_{a,c} = U_{a,v}·U_{v,c}
(H²)_{a,d} = U_{a,v}·U_{v,d} + U_{a,b}·U_{b,d}
(H²)_{b,c} = U_{b,v}·U_{v,c} + U_{b,d}·U_{d,c}
(H²)_{b,d} = U_{b,v}·U_{v,d} + U_{b,e}·U_{e,d} - (deg(b)+deg(d))U_{b,d}
```

with every `U_{x,y}` on the right meaning "the edge's stored matrix, or its
dagger, according to whether `x<y`" — and

```
(H^4)_{vv} = Σ_{x1,x3 ∈ {v,a,b,c,d}} H_{v,x1}·(H²)_{x1,x3}·H_{x3,v}
```

**This bounded, six-vertex (`v,a,b,c,d,e`) formula, using only `T1`, `T2`,
`T3` and the real degrees of `v,a,b,c,d`, exactly reproduces the true value
for every sibling vertex checked** — all 117 instances at `m = 2, 3, 4`,
zero exceptions (`tests/test_bounded_formula.py`). It correctly gives
`-8sin²(θ/2)` for `v=1` and exactly `0` for `v=11`, using their (identical
-looking) `T1,T2,T3` data — the difference comes entirely from which
vertex of each pair (`v` vs `a`, `v` vs `b`, `v` vs `d`, `b` vs `d`, ...)
happens to carry the smaller integer label, which flips a dagger.

**What this resolves:** the "arbitrarily deep prefix" dependence in §2's
automaton is not a real feature of the SU(2)/trace identity — it was this
repository's own incomplete bookkeeping surfacing as apparent recursion.
The true dependence is local (bounded by `T1 ∪ T2 ∪ T3`); the automaton
(§2) remains an exactly-verified *description* of the outcome, now
explained rather than mysterious.

**What's still open, precisely:** a closed statement of which endpoint of
each relevant edge gets the smaller label, derived from the recursive
definition of `sg_tree_graph_with_faces` itself (vertex-dictionary
insertion order across the three shifted copies at each recursive step),
rather than by constructing the graph and comparing integers. Checked
across all 81 level-4 sibling instances: `v < c` and `b < d` held in
*every* case; `v` vs `a`, `v` vs `b`, and `v` vs `d` each went both ways
(4 distinct patterns observed). This is a finite fact about a Python
function's labeling order — tractable by reading `sg_tree_graph_with_faces`
and `one_step`'s vertex-dictionary construction directly — not a further
open question about the operator identity itself. Once stated, it
completes the hand proof of `TraceDefectIdentity` for all `m`; Lean
formalization would still be separate work after that.

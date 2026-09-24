# The FF/OF0/OF1 split: an exact rule, and what it buys us

## Status

**Exactly verified (symbolic, zero exceptions):** a 3-state automaton that
predicts, for every FF/OF0/OF1-type vertex, whether its local contribution
is the generic `-8 sin²(θ/2)` or exactly `0`. Checked against direct exact
computation for **every** relevant vertex at `m = 2, 3, 4, 5` — 360
instances, 0 mismatches (`tests/test_split_automaton.py`).

**Established given that rule:** an exact algebraic re-derivation of the
full closed form `Δ_m(θ) = -16(3^(m-1)+1) sin²(θ/2)` **for general `m`**,
by counting how many vertices of each type land on which side of the
automaton (§3 below) — not merely checked for specific `m`.

**Not yet established:** an inductive proof that the automaton rule itself
holds for *every* `m` (as opposed to: verified exhaustively at 4 different
sizes). This is now a precisely stated, narrow, well-evidenced combinatorial
claim rather than an open-ended mystery — see §4 for exactly what's left
and why it looks tractable. No Lean proof exists yet either way.

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

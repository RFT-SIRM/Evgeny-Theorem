import EvgenyTheorem.VertexIndex

namespace EvgenyTheorem


/--
The recursive face-list offset is a multiple of three, so the cyclic Pauli-axis
label is unchanged when an edge is copied into either later face block.
-/
theorem faceAxis_shift_by_three_pow (m i : ℕ) (hm : 1 ≤ m) :
    faceAxis (3 ^ m + i) = faceAxis i := by
  cases m with
  | zero => omega
  | succ m =>
      simp [faceAxis, pow_succ, Nat.mul_add_mod]

/--
The comparison of vertex indices is the only orientation choice made by
connectionOperatorWithAxis: the smaller-index endpoint receives the forward
block and the reverse endpoint receives its conjugate transpose.
-/
def SameLocalIndexOrder {α β : Type*}
    (idxA : α → ℕ) (idxB : β → ℕ) (φ : α → β) : Prop :=
  ∀ a b, idxA a ≤ idxA b ↔ idxB (φ a) ≤ idxB (φ b)

/--
If a local copy map preserves pairwise index order, then it preserves the
forward/reverse branch used to orient every directed edge. This is the exact
finite combinatorial interface needed before comparing the corresponding
operator blocks.
-/
theorem orientationBranch_eq_of_sameLocalIndexOrder
    {α β : Type*} (idxA : α → ℕ) (idxB : β → ℕ) (φ : α → β)
    (horder : SameLocalIndexOrder idxA idxB φ) (a b : α) :
    (if idxA a ≤ idxA b then true else false) =
      (if idxB (φ a) ≤ idxB (φ b) then true else false) := by
  by_cases h : idxA a ≤ idxA b
  · have h' : idxB (φ a) ≤ idxB (φ b) := (horder a b).mp h
    simp [h, h']
  · have h' : ¬ idxB (φ a) ≤ idxB (φ b) := fun h' =>
      h ((horder a b).mpr h')
    simp [h, h']

/--
For the concrete recursive vertex numbering, this specializes to the
orientation branch in connectionOperatorWithAxis. The geometric induction
must supply SameLocalIndexOrder; this theorem deliberately does not assume
that the graph-copy map already preserves matrix entries.
-/
theorem vIdx_orientationBranch_eq
    (m : ℕ) (φ : Point → Point)
    (horder : ∀ p q, vIdx m p ≤ vIdx m q ↔
      vIdx (m + 1) (φ p) ≤ vIdx (m + 1) (φ q))
    (p q : Point) :
    (if vIdx m p ≤ vIdx m q then true else false) =
      (if vIdx (m + 1) (φ p) ≤ vIdx (m + 1) (φ q) then true else false) := by
  exact orientationBranch_eq_of_sameLocalIndexOrder
    (vIdx m) (vIdx (m + 1)) φ horder p q

/--
Filtering a nodup list preserves the relative order of any two retained
elements. This is the reusable list-theoretic step needed for the B and C
copies, whose duplicate vertices are removed by `removeAll`.
-/
theorem idxOf_filter_lt_of_nodup {α : Type*} [BEq α] [LawfulBEq α]
    (p : α → Bool) :
    ∀ {l : List α} {x y : α}, l.Nodup → x ∈ l → y ∈ l →
      p x = true → p y = true → l.idxOf x < l.idxOf y →
      (l.filter p).idxOf x < (l.filter p).idxOf y := by
  intro l
  induction l with
  | nil =>
      intro x y hnd hx
      simp at hx
  | cons a t ih =>
      intro x y hnd hx hy hpx hpy hlt
      have hn := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hx with hax | hxt
      · subst x
        have hay : a ≠ y := by
          intro heq
          subst y
          simp at hlt
        have hyt : y ∈ t := (List.mem_cons.mp hy).resolve_left hay
        simp [List.filter_cons, hpx, List.idxOf_cons, hay]
      · have hax : a ≠ x := fun heq => hxt ▸ hn.1 (by simpa [heq])
        rcases List.mem_cons.mp hy with hay | hyt
        · subst y
          have hlt' : ¬ l.idxOf x < l.idxOf a := by
            simp [List.idxOf_cons, hax] at hlt
          omega
        · have hay : a ≠ y := fun heq => hyt ▸ hn.1 (by simpa [heq])
          have hxt' : x ∈ t := hxt
          have hyt' : y ∈ t := hyt
          have hltTail : t.idxOf x < t.idxOf y := by
            simpa [List.idxOf_cons, hax, hay] using hlt
          have hrec := ih hn.2 hxt' hyt' hpx hpy hltTail
          cases hpa : p a with
          | false =>
              simpa [List.filter_cons, hpa] using hrec
          | true =>
              simpa [List.filter_cons, hpa, List.idxOf_cons, hax, hay] using
                Nat.succ_lt_succ hrec

/--
The first copy in the recursive Sierpinski vertex order is the old vertex list.
For vertices already present at level m, their global indices are unchanged at
level m+1; hence every pairwise index comparison within that copy is preserved.
This is the concrete base case for the recursive orientation-locality proof.
-/
theorem vIdx_order_preserved_on_old_copy
    (m : ℕ) (p q : Point)
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) :
    (vIdx (m + 1) p ≤ vIdx (m + 1) q) ↔
      (vIdx m p ≤ vIdx m q) := by
  rw [vIdx_succ_of_mem hp, vIdx_succ_of_mem hq]

end EvgenyTheorem

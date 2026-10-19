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

end EvgenyTheorem

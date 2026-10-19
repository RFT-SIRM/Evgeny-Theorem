import EvgenyTheorem.FlipC

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

/--
On a duplicate-free vertex-order list, the index function is injective on
members of that list. This converts strict-order preservation into the
orientation comparison needed by the connection operator.
-/
theorem vIdx_injective_on_vertexOrder (m : ℕ) {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (hidx : vIdx m p = vIdx m q) : p = q := by
  unfold vIdx at hidx
  exact (List.idxOf_inj hp).mp hidx

/-- Strict index order is preserved inside copy A (the old vertices). -/
theorem vIdx_succ_A_lt_iff (m : ℕ) {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) :
    vIdx (m + 1) p < vIdx (m + 1) q ↔ vIdx m p < vIdx m q := by
  rw [vIdx_succ_of_mem hp, vIdx_succ_of_mem hq]

/-- Strict index order is preserved inside the new, non-duplicated part of copy B. -/
theorem vIdx_succ_B_order_bridge {m : ℕ} {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (hp0 : p ≠ (0, 0)) (hq0 : q ≠ (0, 0)) :
    vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 p) <
      vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 q) ↔
    vIdx m p < vIdx m q :=
  vIdx_succ_B_lt_iff hp hq hp0 hq0

/-- Strict index order is preserved inside the new, non-duplicated part of copy C. -/
theorem vIdx_succ_C_order_bridge {m : ℕ} {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (hp0 : p ≠ (0, 0)) (hps : p ≠ (2 ^ m, 0))
    (hq0 : q ≠ (0, 0)) (hqs : q ≠ (2 ^ m, 0)) :
    vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 p) <
      vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 q) ↔
    vIdx m p < vIdx m q :=
  vIdx_succ_C_lt_iff hp hq hp0 hps hq0 hqs

/-- Strict-order preservation upgrades to non-strict-order preservation whenever both index maps are injective. -/
theorem le_iff_of_lt_iff_of_injective
    {α : Type*} (f g : α → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hlt : ∀ a b, f a < f b ↔ g a < g b) (a b : α) :
    f a ≤ f b ↔ g a ≤ g b := by
  constructor
  · intro hab
    by_cases heq : a = b
    · subst b
      exact Nat.le_refl _
    · have hne : f a ≠ f b := fun h => heq (hf h)
      exact Nat.le_of_lt (hlt a b |>.mp (Nat.lt_of_le_of_ne hab hne))
  · intro hab
    by_cases heq : a = b
    · subst b
      exact Nat.le_refl _
    · have hne : g a ≠ g b := fun h => heq (hg h)
      exact Nat.le_of_lt (hlt a b |>.mpr (Nat.lt_of_le_of_ne hab hne))

/-- Copy B: strict-order preservation also preserves the non-strict comparison used for orientation. -/
theorem vIdx_succ_B_le_iff (m : ℕ)
    (a b : {p : Point // p ∈ vertexOrder m ∧ p ≠ (0, 0)}) :
    vIdx m a.1 ≤ vIdx m b.1 ↔
      vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 a.1) ≤
        vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 b.1) := by
  refine le_iff_of_lt_iff_of_injective
    (α := {p : Point // p ∈ vertexOrder m ∧ p ≠ (0, 0)})
    (fun x => vIdx m x.1)
    (fun x => vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 x.1))
    ?_ ?_ ?_ a b
  · intro x y hxy
    exact Subtype.ext (vIdx_injective_on_vertexOrder m x.2.1 y.2.1 hxy)
  · intro x y hxy
    have hx : shiftPoint (2 ^ m) 1 0 x.1 ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inr (Or.inl (List.mem_map.mpr ⟨x.1, x.2.1, rfl⟩))
    have hy : shiftPoint (2 ^ m) 1 0 y.1 ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inr (Or.inl (List.mem_map.mpr ⟨y.1, y.2.1, rfl⟩))
    have hpoints := vIdx_injective_on_vertexOrder (m + 1) hx hy hxy
    exact Subtype.ext (shiftPoint_injective _ _ _ hpoints)
  · intro x y
    exact (vIdx_succ_B_lt_iff x.2.1 y.2.1 x.2.2 y.2.2).symm

/-- Copy C: strict-order preservation also preserves the non-strict comparison used for orientation. -/
theorem vIdx_succ_C_le_iff (m : ℕ)
    (a b : {p : Point // p ∈ vertexOrder m ∧ p ≠ (0, 0) ∧ p ≠ (2 ^ m, 0)}) :
    vIdx m a.1 ≤ vIdx m b.1 ↔
      vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 a.1) ≤
        vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 b.1) := by
  refine le_iff_of_lt_iff_of_injective
    (α := {p : Point // p ∈ vertexOrder m ∧ p ≠ (0, 0) ∧ p ≠ (2 ^ m, 0)})
    (fun x => vIdx m x.1)
    (fun x => vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 x.1))
    ?_ ?_ ?_ a b
  · intro x y hxy
    exact Subtype.ext (vIdx_injective_on_vertexOrder m x.2.1 y.2.1 hxy)
  · intro x y hxy
    have hx : shiftPoint (2 ^ m) 0 1 x.1 ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inr (Or.inr (List.mem_map.mpr ⟨x.1, x.2.1, rfl⟩))
    have hy : shiftPoint (2 ^ m) 0 1 y.1 ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inr (Or.inr (List.mem_map.mpr ⟨y.1, y.2.1, rfl⟩))
    have hpoints := vIdx_injective_on_vertexOrder (m + 1) hx hy hxy
    exact Subtype.ext (shiftPoint_injective _ _ _ hpoints)
  · intro x y
    exact (vIdx_succ_C_lt_iff x.2.1 y.2.1 x.2.2.1 x.2.2.2 y.2.2.1 y.2.2.2).symm

/-- Copy A satisfies the shared order interface on all vertices of the previous level. -/
theorem sameLocalIndexOrder_A (m : ℕ) :
    SameLocalIndexOrder
      (fun x : {p : Point // p ∈ vertexOrder m} => vIdx m x.1)
      (fun p : Point => vIdx (m + 1) p)
      (fun x => x.1) := by
  intro a b
  rw [vIdx_succ_of_mem a.2, vIdx_succ_of_mem b.2]

/-- Copy B satisfies the shared order interface on its genuinely new vertices. -/
theorem sameLocalIndexOrder_B (m : ℕ) :
    SameLocalIndexOrder
      (fun x : {p : Point // p ∈ vertexOrder m ∧ p ≠ (0, 0)} => vIdx m x.1)
      (fun p : Point => vIdx (m + 1) p)
      (fun x => shiftPoint (2 ^ m) 1 0 x.1) := by
  intro a b
  exact vIdx_succ_B_le_iff m a b

/-- Copy C satisfies the shared order interface on its genuinely new vertices. -/
theorem sameLocalIndexOrder_C (m : ℕ) :
    SameLocalIndexOrder
      (fun x : {p : Point // p ∈ vertexOrder m ∧ p ≠ (0, 0) ∧ p ≠ (2 ^ m, 0)} => vIdx m x.1)
      (fun p : Point => vIdx (m + 1) p)
      (fun x => shiftPoint (2 ^ m) 0 1 x.1) := by
  intro a b
  exact vIdx_succ_C_le_iff m a b

end EvgenyTheorem

import EvgenyTheorem.DegSplit
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
  change vIdx m a.1 ≤ vIdx m b.1 ↔
    vIdx (m + 1) a.1 ≤ vIdx (m + 1) b.1
  exact (vIdx_order_preserved_on_old_copy m a.1 b.1 a.2 b.2).symm

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

/-!
## Degree transport for the recursive copies

The six glued states are exactly the points where two copies meet. Away
from those excluded corner points, the recursive degree formula has a single
nonzero copy contribution. These lemmas provide the degree-preservation part
of the radius-two corner transport; they do not yet identify the oriented
matrix entries on the exceptional corner edges.
-/

/-- Copy A preserves degree away from its two far corners, where another copy
can contribute to the degree at the next level. -/
theorem pdeg_succ_A_local
    (m : ℕ) {p : Point} (hp : p ∈ vertexOrder m)
    (hpX : p ≠ (2 ^ m, 0)) (hpY : p ≠ (0, 2 ^ m)) :
    pdeg (m + 1) p = pdeg m p := by
  rcases p with ⟨x, y⟩
  have hsum : x + y ≤ 2 ^ m := vertexOrder_sum_le m (x, y) hp
  have hA : (x, y) ∈ (vertexOrder m).toFinset := List.mem_toFinset.mpr hp
  have hB :
      ¬ (2 ^ m ≤ x ∧ (x - 2 ^ m, y) ∈ (vertexOrder m).toFinset) := by
    rintro ⟨hxs, _⟩
    have hx : x = 2 ^ m := by omega
    have hy : y = 0 := by omega
    exact hpX (Prod.ext hx hy)
  have hC :
      ¬ (2 ^ m ≤ y ∧ (x, y - 2 ^ m) ∈ (vertexOrder m).toFinset) := by
    rintro ⟨hys, _⟩
    have hx : x = 0 := by omega
    have hy : y = 2 ^ m := by omega
    exact hpY (Prod.ext hx hy)
  rw [pdeg_succ, if_pos hA, if_neg hB, if_neg hC]
  simp

/-- Copy B preserves degree away from its two glued corners, whose local
coordinates are (0,0) and (0,2^m). -/
theorem pdeg_succ_B_local
    (m : ℕ) {p : Point} (hp : p ∈ vertexOrder m)
    (hp0 : p ≠ (0, 0)) (hpY : p ≠ (0, 2 ^ m)) :
    pdeg (m + 1) (shiftPoint (2 ^ m) 1 0 p) = pdeg m p := by
  rcases p with ⟨x, y⟩
  simp only [shiftPoint, Nat.one_mul, Nat.zero_mul, Nat.add_zero]
  have hsum : x + y ≤ 2 ^ m := vertexOrder_sum_le m (x, y) hp
  have hpFin : (x, y) ∈ (vertexOrder m).toFinset := List.mem_toFinset.mpr hp
  have hA : (x + 2 ^ m, y) ∉ (vertexOrder m).toFinset := by
    intro h
    have hbound := vertexOrder_sum_le m (x + 2 ^ m, y) (List.mem_toFinset.mp h)
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    exact hp0 (Prod.ext hx hy)
  have hB :
      2 ^ m ≤ x + 2 ^ m ∧
        ((x + 2 ^ m) - 2 ^ m, y) ∈ (vertexOrder m).toFinset := by
    constructor
    · omega
    · simpa [Nat.add_sub_cancel_right] using hpFin
  have hC :
      ¬ (2 ^ m ≤ y ∧ (x + 2 ^ m, y - 2 ^ m) ∈ (vertexOrder m).toFinset) := by
    rintro ⟨hys, _⟩
    have hx : x = 0 := by omega
    have hy : y = 2 ^ m := by omega
    exact hpY (Prod.ext hx hy)
  rw [pdeg_succ, if_neg hA, if_pos hB, if_neg hC]
  simp [Nat.add_sub_cancel_right]

/-- Copy C preserves degree away from its two glued corners, whose local
coordinates are (0,0) and (2^m,0). -/
theorem pdeg_succ_C_local
    (m : ℕ) {p : Point} (hp : p ∈ vertexOrder m)
    (hp0 : p ≠ (0, 0)) (hpX : p ≠ (2 ^ m, 0)) :
    pdeg (m + 1) (shiftPoint (2 ^ m) 0 1 p) = pdeg m p := by
  rcases p with ⟨x, y⟩
  simp only [shiftPoint, Nat.zero_mul, Nat.one_mul, Nat.add_zero]
  have hsum : x + y ≤ 2 ^ m := vertexOrder_sum_le m (x, y) hp
  have hpFin : (x, y) ∈ (vertexOrder m).toFinset := List.mem_toFinset.mpr hp
  have hA : (x, y + 2 ^ m) ∉ (vertexOrder m).toFinset := by
    intro h
    have hbound := vertexOrder_sum_le m (x, y + 2 ^ m) (List.mem_toFinset.mp h)
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    exact hp0 (Prod.ext hx hy)
  have hB :
      ¬ (2 ^ m ≤ x ∧ (x - 2 ^ m, y + 2 ^ m) ∈ (vertexOrder m).toFinset) := by
    rintro ⟨hxs, _⟩
    have hx : x = 2 ^ m := by omega
    have hy : y = 0 := by omega
    exact hpX (Prod.ext hx hy)
  have hC :
      2 ^ m ≤ y + 2 ^ m ∧
        (x, (y + 2 ^ m) - 2 ^ m) ∈ (vertexOrder m).toFinset := by
    constructor
    · omega
    · simpa [Nat.add_sub_cancel_right] using hpFin
  rw [pdeg_succ, if_neg hA, if_neg hB, if_pos hC]
  simp [Nat.add_sub_cancel_right]

end EvgenyTheorem

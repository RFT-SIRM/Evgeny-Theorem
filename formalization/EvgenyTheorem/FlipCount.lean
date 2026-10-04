import EvgenyTheorem.FlipFaces

namespace EvgenyTheorem

def flippedB (m : ℕ) (f : Face) : Bool := decide (vIdx m f.2.1 < vIdx m f.1)

def cornerB (m : ℕ) (f : Face) : Bool := decide (f.2.1 = (2 ^ m, 0))

/-- Number of faces whose flux edge is directed against the +x direction by the numbering. -/
def flipCount (m : ℕ) : ℕ := (facesExact m).countP (flippedB m)

theorem countP_or_of_disjoint {α : Type*} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, ¬ (p x = true ∧ q x = true)) →
      l.countP (fun x => p x || q x) = l.countP p + l.countP q
  | [], _ => by simp
  | x :: xs, h => by
    have hx : ¬ (p x = true ∧ q x = true) := h x (by simp)
    have ih := countP_or_of_disjoint p q xs (fun y hy => h y (by simp [hy]))
    simp only [List.countP_cons, ih]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

theorem shiftPoint_B_eq_corner (m : ℕ) (q : Point) :
    shiftPoint (2 ^ m) 1 0 q = (2 ^ (m + 1), 0) ↔ q = (2 ^ m, 0) := by
  rcases q with ⟨x, y⟩
  simp only [shiftPoint, Prod.mk.injEq, pow_succ]
  omega

theorem shiftPoint_C_ne_corner (m : ℕ) (q : Point) :
    shiftPoint (2 ^ m) 0 1 q ≠ (2 ^ (m + 1), 0) := by
  rcases q with ⟨x, y⟩
  intro h
  simp only [shiftPoint, Prod.mk.injEq] at h
  have : 2 ^ m ≥ 1 := Nat.one_le_two_pow
  omega

/-- Exactly one face has the corner `(2^m, 0)` as its second endpoint. -/
theorem corner_count (m : ℕ) : (facesExact m).countP (cornerB m) = 1 := by
  induction m with
  | zero => first | decide | simp [facesExact, cornerB]
  | succ m ih =>
    simp only [facesExact]
    rw [List.countP_append, List.countP_append, List.countP_map, List.countP_map,
      List.countP_map]
    have hA : (facesExact m).countP (cornerB (m + 1) ∘ shiftFace (2 ^ m) 0 0) = 0 := by
      rw [List.countP_eq_zero]
      intro f hf
      obtain ⟨_, hb⟩ := face_endpoints_mem m f hf
      have hbnd := vertexOrder_sum_le m _ hb
      have hp : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [Function.comp, cornerB, shiftFace_zero', decide_eq_true_eq]
      intro h
      have := congrArg Prod.fst h
      simp only at this
      have h2 : 2 ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
      have : 2 ^ m ≥ 1 := Nat.one_le_two_pow
      omega
    have hB : (facesExact m).countP (cornerB (m + 1) ∘ shiftFace (2 ^ m) 1 0) =
        (facesExact m).countP (cornerB m) := by
      apply List.countP_congr
      intro f hf
      simp only [Function.comp, cornerB, decide_eq_true_eq]
      exact shiftPoint_B_eq_corner m f.2.1
    have hC : (facesExact m).countP (cornerB (m + 1) ∘ shiftFace (2 ^ m) 0 1) = 0 := by
      rw [List.countP_eq_zero]
      intro f hf
      simp only [Function.comp, cornerB, decide_eq_true_eq]
      exact shiftPoint_C_ne_corner m f.2.1
    rw [hA, hB, hC, ih]

/-- **Recursion for the number of flipped faces.** -/
theorem flipCount_succ {m : ℕ} (hm : 1 ≤ m) : flipCount (m + 1) = 3 * flipCount m + 1 := by
  unfold flipCount
  simp only [facesExact]
  rw [List.countP_append, List.countP_append, List.countP_map, List.countP_map,
    List.countP_map]
  have hA : (facesExact m).countP (flippedB (m + 1) ∘ shiftFace (2 ^ m) 0 0) =
      (facesExact m).countP (flippedB m) := by
    apply List.countP_congr
    intro f hf
    have := flipped_A m f hf
    simp only [Function.comp, flippedB, decide_eq_true_eq]
    exact this
  have hB : (facesExact m).countP (flippedB (m + 1) ∘ shiftFace (2 ^ m) 1 0) =
      (facesExact m).countP (flippedB m) := by
    apply List.countP_congr
    intro f hf
    have := flipped_B m f hf
    simp only [Function.comp, flippedB, decide_eq_true_eq]
    exact this
  have hC : (facesExact m).countP (flippedB (m + 1) ∘ shiftFace (2 ^ m) 0 1) =
      (facesExact m).countP (fun f => flippedB m f || cornerB m f) := by
    apply List.countP_congr
    intro f hf
    have := flipped_C m hm f hf
    simp only [Function.comp, flippedB, cornerB, Bool.or_eq_true, decide_eq_true_eq]
    exact this
  have hD : (facesExact m).countP (fun f => flippedB m f || cornerB m f) =
      (facesExact m).countP (flippedB m) + (facesExact m).countP (cornerB m) := by
    apply countP_or_of_disjoint
    intro f hf
    rintro ⟨h1, h2⟩
    simp only [flippedB, cornerB, decide_eq_true_eq] at h1 h2
    obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
    have hfst := congrArg Prod.fst h2
    have hsnd := congrArg Prod.snd h2
    simp only at hfst hsnd
    have ha : f.1 = (2 ^ m - 1, 0) := by
      ext
      · simp only; omega
      · simp only; omega
    have hlt := bottom_lt m hm
    rw [ha, h2] at h1
    exact absurd h1 (not_lt.mpr (le_of_lt hlt))
  rw [hA, hB, hC, hD, corner_count]
  omega

theorem flipCount_one : flipCount 1 = 0 := by
  first | decide | rfl

/-- `F_m = (3^(m-1) - 1) / 2`, stated without division. -/
theorem flipCount_closed : ∀ m : ℕ, 2 * flipCount (m + 1) + 1 = 3 ^ m
  | 0 => by rw [flipCount_one]; simp
  | m + 1 => by
    have h := flipCount_succ (m := m + 1) (by omega)
    have ih := flipCount_closed m
    rw [h, pow_succ]
    omega

end EvgenyTheorem

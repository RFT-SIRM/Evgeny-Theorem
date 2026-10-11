import EvgenyTheorem.GlueBridge
import EvgenyTheorem.OpSplit2

/-!
# Concrete gluing data for `SG(m) ⊔ SG(m) ⊔ SG(m) → SG(m+1)`

* `WSG m = GCopy × Pt m × C2` : three disjoint copies of the level-`m` index set.
* `sgπ m` : the map into the level-`(m+1)` index set (shift by `(0,0)`, `(2^m,0)`, `(0,2^m)`).
* `sgGlue m` : the `GlueData` whose glued points are the six corner points that get identified.
* `sgπ_iff` : the fibres of `sgπ` are exactly singletons and glued pairs (`hπ` of `GlueBridge`).
-/

namespace EvgenyTheorem

open Matrix

/-- Names of the three copies. -/
inductive GCopy
  | A | B | C
  deriving DecidableEq

instance : Fintype GCopy :=
  ⟨{GCopy.A, GCopy.B, GCopy.C}, fun x => by cases x <;> simp⟩

/-- Shift of the copy `c` inside `SG(m+1)`. -/
def GCopy.shift (m : ℕ) : GCopy → Point → Point
  | .A => shiftPoint (2 ^ m) 0 0
  | .B => shiftPoint (2 ^ m) 1 0
  | .C => shiftPoint (2 ^ m) 0 1

theorem GCopy.shift_mem (m : ℕ) (c : GCopy) {p : Point} (hp : p ∈ vertexOrder m) :
    c.shift m p ∈ vertexOrder (m + 1) := by
  rw [mem_vertexOrder_succ_iff]
  cases c
  · left
    simpa [GCopy.shift, shiftPoint] using hp
  · right; left
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  · right; right
    exact List.mem_map.mpr ⟨p, hp, rfl⟩

/-- `(c, p)` and `(c', p')` are the two sides of one identified corner. -/
def gl (m : ℕ) (c : GCopy) (p : Point) (c' : GCopy) (p' : Point) : Prop :=
  (c = .A ∧ p = (2 ^ m, 0) ∧ c' = .B ∧ p' = (0, 0)) ∨
  (c = .B ∧ p = (0, 0) ∧ c' = .A ∧ p' = (2 ^ m, 0)) ∨
  (c = .A ∧ p = (0, 2 ^ m) ∧ c' = .C ∧ p' = (0, 0)) ∨
  (c = .C ∧ p = (0, 0) ∧ c' = .A ∧ p' = (0, 2 ^ m)) ∨
  (c = .B ∧ p = (0, 2 ^ m) ∧ c' = .C ∧ p' = (2 ^ m, 0)) ∨
  (c = .C ∧ p = (2 ^ m, 0) ∧ c' = .B ∧ p' = (0, 2 ^ m))

/-- Two shifted points coincide iff they are the same point of the same copy,
or the two sides of an identified corner. -/
theorem shift_eq_iff (m : ℕ) {c c' : GCopy} {p p' : Point}
    (hp : p ∈ vertexOrder m) (hp' : p' ∈ vertexOrder m) :
    c.shift m p = c'.shift m p' ↔ (c = c' ∧ p = p') ∨ gl m c p c' p' := by
  have h1 := vertexOrder_sum_le m p hp
  have h2 := vertexOrder_sum_le m p' hp'
  have h3 : 0 < 2 ^ m := by positivity
  cases c <;> cases c' <;>
    simp [GCopy.shift, shiftPoint, gl, Prod.ext_iff] <;> omega

theorem gl_unique (m : ℕ) {c c1 c2 : GCopy} {p p1 p2 : Point}
    (h1 : gl m c p c1 p1) (h2 : gl m c p c2 p2) : c1 = c2 ∧ p1 = p2 := by
  have h3 : 0 < 2 ^ m := by positivity
  cases c <;> cases c1 <;> cases c2 <;>
    simp [gl, Prod.ext_iff] at h1 h2 ⊢ <;> omega

theorem gl_symm {m : ℕ} {c c' : GCopy} {p p' : Point} (h : gl m c p c' p') :
    gl m c' p' c p := by
  rcases h with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ |
    ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · exact Or.inr (Or.inl ⟨c, d, a, b⟩)
  · exact Or.inl ⟨c, d, a, b⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, d, a, b⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨c, d, a, b⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, d, a, b⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, d, a, b⟩))))

theorem gl_ne {m : ℕ} {c c' : GCopy} {p p' : Point} (h : gl m c p c' p') : c ≠ c' := by
  rintro rfl
  rcases h with ⟨h1, -, h2, -⟩ | ⟨h1, -, h2, -⟩ | ⟨h1, -, h2, -⟩ | ⟨h1, -, h2, -⟩ |
    ⟨h1, -, h2, -⟩ | ⟨h1, -, h2, -⟩ <;>
    exact absurd (h1.symm.trans h2) (by decide)

/-! ### The index set and the glue data -/

/-- Three disjoint copies of the level-`m` index set (with spin). -/
abbrev WSG (m : ℕ) := GCopy × Pt m × C2

def glW (m : ℕ) (w w' : WSG m) : Prop :=
  gl m w.1 w.2.1.1 w'.1 w'.2.1.1 ∧ w.2.2 = w'.2.2

theorem glW_symm {m : ℕ} {w w' : WSG m} (h : glW m w w') : glW m w' w :=
  ⟨gl_symm h.1, h.2.symm⟩

theorem glW_unique {m : ℕ} {w a b : WSG m} (ha : glW m w a) (hb : glW m w b) : a = b := by
  obtain ⟨e1, e2⟩ := gl_unique m ha.1 hb.1
  exact Prod.ext e1 (Prod.ext (Subtype.ext e2) (ha.2.symm.trans hb.2))

open Classical in
/-- The partner of `w` (or `w` itself if `w` is not glued). -/
noncomputable def sgσ (m : ℕ) (w : WSG m) : WSG m :=
  if h : ∃ w', glW m w w' then h.choose else w

theorem glW_sgσ {m : ℕ} {w : WSG m} (h : ∃ w', glW m w w') : glW m w (sgσ m w) := by
  unfold sgσ
  rw [dif_pos h]
  exact h.choose_spec

/-- The concrete gluing data of `SG(m)`. -/
noncomputable def sgGlue (m : ℕ) : GlueData (fun w : WSG m => w.1) where
  g w := ∃ w', glW m w w'
  dg := fun _ => Classical.propDecidable _
  σ := sgσ m
  g_σ := fun w hw => ⟨w, glW_symm (glW_sgσ hw)⟩
  σσ := fun w hw => by
    have h1 := glW_sgσ hw
    have h2 : ∃ w', glW m (sgσ m w) w' := ⟨w, glW_symm h1⟩
    have h3 := glW_sgσ h2
    exact (glW_unique (glW_symm h1) h3).symm
  cp_σ := fun w hw => (gl_ne (glW_sgσ hw).1).symm

/-- The map from the three copies to the level-`(m+1)` index set. -/
def sgπ (m : ℕ) (w : WSG m) : Pt (m + 1) × C2 :=
  (⟨w.1.shift m w.2.1.1,
    List.mem_toFinset.mpr (GCopy.shift_mem m w.1 (List.mem_toFinset.mp w.2.1.2))⟩, w.2.2)

/-- **Fibres of `sgπ`**: singletons and glued pairs (the hypothesis `hπ` of `GlueBridge`). -/
theorem sgπ_iff (m : ℕ) (w w' : WSG m) :
    sgπ m w = sgπ m w' ↔ (w = w' ∨ ((sgGlue m).g w ∧ w' = (sgGlue m).σ w)) := by
  have hp := List.mem_toFinset.mp w.2.1.2
  have hp' := List.mem_toFinset.mp w'.2.1.2
  constructor
  · intro h
    have hs : w.1.shift m w.2.1.1 = w'.1.shift m w'.2.1.1 := congrArg (fun x => x.1.1) h
    have hi : w.2.2 = w'.2.2 := by
      have h2 := congrArg Prod.snd h
      exact h2
    rcases (shift_eq_iff m hp hp').mp hs with ⟨e1, e2⟩ | hg
    · left
      exact Prod.ext e1 (Prod.ext (Subtype.ext e2) hi)
    · right
      have hw : glW m w w' := ⟨hg, hi⟩
      have hex : ∃ w'', glW m w w'' := ⟨w', hw⟩
      exact ⟨hex, glW_unique hw (glW_sgσ hex)⟩
  · rintro (h | ⟨hex, h'⟩)
    · rw [h]
    · have hg := glW_sgσ hex
      have hq := List.mem_toFinset.mp (sgσ m w).2.1.2
      rw [h']
      exact Prod.ext (Subtype.ext ((shift_eq_iff m hp hq).mpr (Or.inr hg.1))) hg.2

/-- **Gluing identity for the actual `SG(m) → SG(m+1)` pushforward.** -/
theorem sg_trace4_glue (m : ℕ) (K : Matrix (WSG m) (WSG m) ℂ)
    (hbd : BD (fun w : WSG m => w.1) K)
    (hkg : ∀ w w', (sgGlue m).g w → (sgGlue m).g w' → w.1 = w'.1 → w ≠ w' → K w w' = 0)
    (hu2 : GlueDiag (sgGlue m) (K * K)) :
    Matrix.trace ((Emat (sgπ m) * K * (Emat (sgπ m))ᵀ) * (Emat (sgπ m) * K * (Emat (sgπ m))ᵀ) *
        (Emat (sgπ m) * K * (Emat (sgπ m))ᵀ) * (Emat (sgπ m) * K * (Emat (sgπ m))ᵀ)) =
      Matrix.trace (K * K * K * K) +
        4 * ∑ a, (if (sgGlue m).g a then (K * K * K) a a * K ((sgGlue m).σ a) ((sgGlue m).σ a)
          else 0) +
        2 * ∑ a, (if (sgGlue m).g a then (K * K) a a * (K * K) ((sgGlue m).σ a) ((sgGlue m).σ a)
          else 0) +
        ∑ a, (if (sgGlue m).g a then K a a * K a a * (K ((sgGlue m).σ a) ((sgGlue m).σ a) *
          K ((sgGlue m).σ a) ((sgGlue m).σ a)) else 0) :=
  trace4_glue_formula (sgGlue m) (sgπ m) (sgπ_iff m) K hbd hkg hu2

end EvgenyTheorem

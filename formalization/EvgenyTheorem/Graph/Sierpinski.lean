import Mathlib

namespace EvgenyTheorem

/-- Integer coordinates of the level-m Sierpiński gasket, scaled by 2^m.
The three recursive copies are glued automatically because vertices are
represented by their coordinates. -/
def InSG : ℕ → ℕ → ℕ → Prop
  | 0, x, y => x + y ≤ 1
  | m + 1, x, y =>
      let s := 2 ^ m
      (x ≤ s ∧ y ≤ s ∧ InSG m x y) ∨
      (s ≤ x ∧ y ≤ s ∧ InSG m (x - s) y) ∨
      (x ≤ s ∧ s ≤ y ∧ InSG m x (y - s))

instance inSGDecidable (m x y : ℕ) : Decidable (InSG m x y) := by
  induction m generalizing x y with
  | zero =>
      change Decidable (x + y ≤ 1)
      infer_instance
  | succ m ih =>
      letI h₁ : Decidable (InSG m x y) := ih x y
      letI h₂ : Decidable (InSG m (x - 2 ^ m) y) := ih (x - 2 ^ m) y
      letI h₃ : Decidable (InSG m x (y - 2 ^ m)) := ih x (y - 2 ^ m)
      simp only [InSG]
      infer_instance

def Vertex (m : ℕ) :=
  {p : Fin (2 ^ m + 1) × Fin (2 ^ m + 1) // InSG m p.1 p.2}

/-- `Vertex m` is a `Fintype` because `InSG` is decidable (`inSGDecidable`)
and it is a subtype of the finite type `Fin (2^m+1) × Fin (2^m+1)`.
Fully computable: no `Fintype.ofFinite`, no `classical`. -/
instance Vertex.fintype (m : ℕ) : Fintype (Vertex m) :=
  Subtype.fintype _

instance Vertex.decidableEq (m : ℕ) : DecidableEq (Vertex m) :=
  Subtype.instDecidableEq

private def stepEdge (p q : ℕ × ℕ) : Prop :=
  (p.1 + 1 = q.1 ∧ p.2 = q.2) ∨
  (p.1 = q.1 ∧ p.2 + 1 = q.2) ∨
  (p.1 + 1 = q.1 ∧ q.2 + 1 = p.2) ∨
  (q.1 + 1 = p.1 ∧ q.2 = p.2) ∨
  (q.1 = p.1 ∧ q.2 + 1 = p.2) ∨
  (q.1 + 1 = p.1 ∧ p.2 + 1 = q.2)

def EdgeB : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, x, y, X, Y =>
      (x == 0 && y == 0 && X == 1 && Y == 0) ||
      (x == 1 && y == 0 && X == 0 && Y == 0) ||
      (x == 1 && y == 0 && X == 0 && Y == 1) ||
      (x == 0 && y == 1 && X == 1 && Y == 0) ||
      (x == 0 && y == 0 && X == 0 && Y == 1) ||
      (x == 0 && y == 1 && X == 0 && Y == 0)
  | m + 1, x, y, X, Y =>
      let s := 2 ^ m
      ((x ≤ s && y ≤ s && X ≤ s && Y ≤ s &&
          EdgeB m x y X Y) ||
       (s ≤ x && y ≤ s && s ≤ X && Y ≤ s &&
          EdgeB m (x - s) y (X - s) Y) ||
       (x ≤ s && s ≤ y && X ≤ s && s ≤ Y &&
          EdgeB m x (y - s) X (Y - s)))

def Adj {m : ℕ} (u v : Vertex m) : Prop :=
  EdgeB m
    (u.1.1 : ℕ) (u.1.2 : ℕ)
    (v.1.1 : ℕ) (v.1.2 : ℕ) = true

/-- `Adj u v` unfolds (definitionally) to a `Bool` equality, which is
always decidable; `inferInstanceAs` sees through the `def` where plain
typeclass search would not. -/
instance Adj.decidable {m : ℕ} (u v : Vertex m) : Decidable (Adj u v) :=
  inferInstanceAs
    (Decidable (EdgeB m (u.1.1 : ℕ) (u.1.2 : ℕ) (v.1.1 : ℕ) (v.1.2 : ℕ) = true))


 
end EvgenyTheorem

namespace EvgenyTheorem

theorem EdgeB_symm (m x y X Y : ℕ) :
    EdgeB m x y X Y = EdgeB m X Y x y := by
  induction m generalizing x y X Y with
  | zero =>
      simp [EdgeB, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc,
        Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
  | succ m ih =>
      simp [EdgeB, ih, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc,
        Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]

theorem Adj_symm {m : ℕ} (u v : Vertex m) :
    Adj u v ↔ Adj v u := by
  simp [Adj, EdgeB_symm]

end EvgenyTheorem

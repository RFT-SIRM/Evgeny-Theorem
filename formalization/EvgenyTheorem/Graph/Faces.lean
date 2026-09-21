import EvgenyTheorem.Graph.Sierpinski

namespace EvgenyTheorem

abbrev Point := ℕ × ℕ
abbrev Face := Point × Point × Point

def shiftPoint (s dx dy : ℕ) (p : Point) : Point :=
  (p.1 + dx * s, p.2 + dy * s)

def shiftFace (s dx dy : ℕ) (f : Face) : Face :=
  (shiftPoint s dx dy f.1,
   shiftPoint s dx dy f.2.1,
   shiftPoint s dx dy f.2.2)

def facesExact : ℕ → List Face
  | 0 => [((0, 0), (1, 0), (0, 1))]
  | m + 1 =>
      let s := 2 ^ m
      let prev := facesExact m
      prev.map (shiftFace s 0 0) ++
      prev.map (shiftFace s 1 0) ++
      prev.map (shiftFace s 0 1)

theorem facesExact_length (m : ℕ) :
    (facesExact m).length = 3 ^ m := by
  induction m with
  | zero =>
      simp [facesExact]
  | succ m ih =>
      simp [facesExact, ih, pow_succ]
      ring

def fluxEdge (f : Face) : Point × Point :=
  if f.1 ≤ f.2.1 then (f.1, f.2.1) else (f.2.1, f.1)

def fluxEdges (m : ℕ) : List (Point × Point) :=
  (facesExact m).map fluxEdge

def fluxValid (m : ℕ) : Bool :=
  (fluxEdges m).all fun e =>
    EdgeB m e.1.1 e.1.2 e.2.1 e.2.2


def PointInBox (m : ℕ) (p : Point) : Prop :=
  p.1 ≤ 2 ^ m ∧ p.2 ≤ 2 ^ m

theorem face_bounds (m : ℕ) (f : Face)
    (hf : f ∈ facesExact m) :
    PointInBox m f.1 ∧
    PointInBox m f.2.1 ∧
    PointInBox m f.2.2 := by
  induction m generalizing f with
  | zero =>
      simp [facesExact, PointInBox] at hf ⊢
      rcases hf with rfl
      norm_num
  | succ m ih =>
      simp [facesExact] at hf
      rcases hf with hf | hf | hf
      · rcases hf with ⟨a, b, c, d, e, f, hf, rfl⟩
        have h := ih ((a, b), (c, d), (e, f)) hf
        simp [PointInBox, shiftFace, shiftPoint, pow_succ] at h ⊢
        omega
      · rcases hf with ⟨a, b, c, d, e, f, hf, rfl⟩
        have h := ih ((a, b), (c, d), (e, f)) hf
        simp [PointInBox, shiftFace, shiftPoint, pow_succ] at h ⊢
        omega
      · rcases hf with ⟨a, b, c, d, e, f, hf, rfl⟩
        have h := ih ((a, b), (c, d), (e, f)) hf
        simp [PointInBox, shiftFace, shiftPoint, pow_succ] at h ⊢
        omega

theorem flux_edge_shape (m : ℕ) (f : Face)
    (hf : f ∈ facesExact m) :
    f.1.1 + 1 = f.2.1.1 ∧ f.1.2 = f.2.1.2 := by
  induction m generalizing f with
  | zero =>
      simp [facesExact] at hf
      rcases hf with rfl
      norm_num
  | succ m ih =>
      simp [facesExact] at hf
      rcases hf with hf | hf | hf
      · rcases hf with ⟨a, b, c, d, e, f, hf, rfl⟩
        have h := ih ((a, b), (c, d), (e, f)) hf
        simp [shiftFace, shiftPoint] at h ⊢
        constructor <;> omega
      · rcases hf with ⟨a, b, c, d, e, f, hf, rfl⟩
        have h := ih ((a, b), (c, d), (e, f)) hf
        simp [shiftFace, shiftPoint] at h ⊢
        constructor <;> omega
      · rcases hf with ⟨a, b, c, d, e, f, hf, rfl⟩
        have h := ih ((a, b), (c, d), (e, f)) hf
        simp [shiftFace, shiftPoint] at h ⊢
        constructor <;> omega

theorem flux_edge_order (m : ℕ) (f : Face)
    (hf : f ∈ facesExact m) :
    f.1 ≤ f.2.1 := by
  have h := flux_edge_shape m f hf
  simp only [Prod.le_def]
  omega

theorem flux_block_disjoint_01 (m : ℕ) (f g : Face)
    (hf : f ∈ facesExact m) (hg : g ∈ facesExact m) :
    fluxEdge (shiftFace (2 ^ m) 0 0 f) ≠
      fluxEdge (shiftFace (2 ^ m) 1 0 g) := by
  have hf_shape := flux_edge_shape m f hf
  have hg_shape := flux_edge_shape m g hg
  have hf_box := face_bounds m f hf
  have hg_box := face_bounds m g hg
  rcases hf_shape with ⟨hf_x, hf_y⟩
  rcases hg_shape with ⟨hg_x, hg_y⟩
  rcases hf_box with ⟨hf_box1, hf_box2, hf_box3⟩
  rcases hg_box with ⟨hg_box1, hg_box2, hg_box3⟩
  have hf_order := flux_edge_order m f hf
  have hg_shift_order :
      (shiftFace (2 ^ m) 1 0 g).1 ≤
        (shiftFace (2 ^ m) 1 0 g).2.1 := by
    simp [shiftFace, shiftPoint, Prod.le_def]
    omega
  simp [PointInBox] at hf_box1 hf_box2 hf_box3 hg_box1 hg_box2 hg_box3
  have hleft_f : f.1.1 < 2 ^ m := by
    omega
  have hleft_g : 2 ^ m ≤ g.1.1 + 2 ^ m := by
    omega
  simp only [fluxEdge]
  rw [if_pos hg_shift_order]
  have hf_shift_order :
      (shiftFace (2 ^ m) 0 0 f).1 ≤
        (shiftFace (2 ^ m) 0 0 f).2.1 := by
    simp [shiftFace, shiftPoint, Prod.le_def]
    omega
  rw [if_pos hf_shift_order]
  simp [shiftFace, shiftPoint]
  intro h
  have hx : f.1.1 = g.1.1 + 2 ^ m := by
    exact congrArg (fun p : Point => p.1) h
  omega


theorem flux_edge_y_lt (m : ℕ) (f : Face)
    (hf : f ∈ facesExact m) :
    f.1.2 < 2 ^ m := by
  induction m generalizing f with
  | zero =>
      simp [facesExact] at hf
      rcases hf with rfl
      norm_num
  | succ m ih =>
      simp [facesExact] at hf
      rcases hf with hf | hf | hf
      · rcases hf with ⟨a, b, c, d, e, f, hf, rfl⟩
        have h := ih ((a, b), (c, d), (e, f)) hf
        simp [shiftFace, shiftPoint, pow_succ] at h ⊢
        omega
      · rcases hf with ⟨a, b, c, d, e, f, hf, rfl⟩
        have h := ih ((a, b), (c, d), (e, f)) hf
        simp [shiftFace, shiftPoint, pow_succ] at h ⊢
        omega
      · rcases hf with ⟨a, b, c, d, e, f, hf, rfl⟩
        have h := ih ((a, b), (c, d), (e, f)) hf
        simp [shiftFace, shiftPoint, pow_succ] at h ⊢
        omega

theorem flux_block_disjoint_02 (m : ℕ) (f g : Face)
    (hf : f ∈ facesExact m) (hg : g ∈ facesExact m) :
    fluxEdge (shiftFace (2 ^ m) 0 0 f) ≠
      fluxEdge (shiftFace (2 ^ m) 0 1 g) := by
  have hf_shape := flux_edge_shape m f hf
  have hg_shape := flux_edge_shape m g hg
  have hf_y := flux_edge_y_lt m f hf
  have hg_y := flux_edge_y_lt m g hg
  have hf_order :
      (shiftFace (2 ^ m) 0 0 f).1 ≤
        (shiftFace (2 ^ m) 0 0 f).2.1 := by
    simp [shiftFace, shiftPoint, Prod.le_def]
    omega
  have hg_order :
      (shiftFace (2 ^ m) 0 1 g).1 ≤
        (shiftFace (2 ^ m) 0 1 g).2.1 := by
    simp [shiftFace, shiftPoint, Prod.le_def]
    omega
  simp only [fluxEdge]
  rw [if_pos hf_order, if_pos hg_order]
  simp [shiftFace, shiftPoint]
  intro h
  have hy : f.1.2 = g.1.2 + 2 ^ m := by
    exact congrArg (fun p : Point => p.2) h
  omega

theorem flux_block_disjoint_12 (m : ℕ) (f g : Face)
    (hf : f ∈ facesExact m) (hg : g ∈ facesExact m) :
    fluxEdge (shiftFace (2 ^ m) 1 0 f) ≠
      fluxEdge (shiftFace (2 ^ m) 0 1 g) := by
  have hf_shape := flux_edge_shape m f hf
  have hg_shape := flux_edge_shape m g hg
  have hf_box := face_bounds m f hf
  have hg_box := face_bounds m g hg
  rcases hf_shape with ⟨hf_x, hf_y⟩
  rcases hg_shape with ⟨hg_x, hg_y⟩
  rcases hf_box with ⟨hf_box1, hf_box2, hf_box3⟩
  rcases hg_box with ⟨hg_box1, hg_box2, hg_box3⟩
  simp [PointInBox] at hf_box1 hf_box2 hf_box3 hg_box1 hg_box2 hg_box3
  have hf_order :
      (shiftFace (2 ^ m) 1 0 f).1 ≤
        (shiftFace (2 ^ m) 1 0 f).2.1 := by
    simp [shiftFace, shiftPoint, Prod.le_def]
    omega
  have hg_order :
      (shiftFace (2 ^ m) 0 1 g).1 ≤
        (shiftFace (2 ^ m) 0 1 g).2.1 := by
    simp [shiftFace, shiftPoint, Prod.le_def]
    omega
  simp only [fluxEdge]
  rw [if_pos hf_order, if_pos hg_order]
  simp [shiftFace, shiftPoint]
  intro h
  have hx : f.1.1 + 2 ^ m = g.1.1 := h
  omega

def shiftEdge (s dx dy : ℕ) (e : Point × Point) : Point × Point :=
  (shiftPoint s dx dy e.1, shiftPoint s dx dy e.2)

theorem shiftEdge_injective (s dx dy : ℕ) :
    Function.Injective (shiftEdge s dx dy) := by
  intro e₁ e₂ h
  rcases e₁ with ⟨p₁, q₁⟩
  rcases e₂ with ⟨p₂, q₂⟩
  simp [shiftEdge, shiftPoint] at h
  rcases h with ⟨hp, hq⟩
  rcases p₁ with ⟨x₁, y₁⟩
  rcases p₂ with ⟨x₂, y₂⟩
  rcases q₁ with ⟨z₁, w₁⟩
  rcases q₂ with ⟨z₂, w₂⟩
  simp_all

theorem fluxEdge_shift (m dx dy : ℕ) (f : Face)
    (hf : f ∈ facesExact m) :
    fluxEdge (shiftFace (2 ^ m) dx dy f) =
      shiftEdge (2 ^ m) dx dy (fluxEdge f) := by
  have horder : f.1 ≤ f.2.1 := by
    exact flux_edge_order m f hf
  have hshift :
      (shiftFace (2 ^ m) dx dy f).1 ≤
        (shiftFace (2 ^ m) dx dy f).2.1 := by
    simp [shiftFace, shiftPoint, Prod.le_def]
    omega
  simp only [fluxEdge]
  rw [if_pos horder, if_pos hshift]
  rfl

theorem fluxEdges_nodup (m : ℕ) : (fluxEdges m).Nodup := by
  induction m with
  | zero =>
      simp [fluxEdges, facesExact, fluxEdge]
  | succ m ih =>
      let s := 2 ^ m
      let B0 := List.map (fun f => fluxEdge (shiftFace s 0 0 f)) (facesExact m)
      let B1 := List.map (fun f => fluxEdge (shiftFace s 1 0 f)) (facesExact m)
      let B2 := List.map (fun f => fluxEdge (shiftFace s 0 1 f)) (facesExact m)

      have map_shift :
          ∀ (dx dy : ℕ) (l : List Face),
            (∀ f ∈ l, f ∈ facesExact m) →
              List.map (fun f => fluxEdge (shiftFace s dx dy f)) l =
                List.map (shiftEdge s dx dy) (List.map fluxEdge l) := by
        intro dx dy l
        induction l with
        | nil =>
            intro _
            rfl
        | cons f l ihl =>
            intro hl
            have hf : f ∈ facesExact m := hl f (by simp)
            have htail : ∀ g ∈ l, g ∈ facesExact m := by
              intro g hg
              exact hl g (by simp [hg])
            simp only [List.map_cons]
            rw [fluxEdge_shift m dx dy f hf, ihl htail]

      have h0 :
          B0 = List.map (shiftEdge s 0 0) (fluxEdges m) := by
        dsimp [B0, fluxEdges]
        exact map_shift 0 0 (facesExact m) (by
          intro f hf
          exact hf)

      have h1 :
          B1 = List.map (shiftEdge s 1 0) (fluxEdges m) := by
        dsimp [B1, fluxEdges]
        exact map_shift 1 0 (facesExact m) (by
          intro f hf
          exact hf)

      have h2 :
          B2 = List.map (shiftEdge s 0 1) (fluxEdges m) := by
        dsimp [B2, fluxEdges]
        exact map_shift 0 1 (facesExact m) (by
          intro f hf
          exact hf)

      have d0 : B0.Nodup := by
        rw [h0]
        exact List.Nodup.map (shiftEdge_injective s 0 0) ih

      have d1 : B1.Nodup := by
        rw [h1]
        exact List.Nodup.map (shiftEdge_injective s 1 0) ih

      have d2 : B2.Nodup := by
        rw [h2]
        exact List.Nodup.map (shiftEdge_injective s 0 1) ih

      have dj01 : B0.Disjoint B1 := by
        rw [List.disjoint_left]
        intro e he0 he1
        rcases List.mem_map.mp he0 with ⟨f, hf, rfl⟩
        rcases List.mem_map.mp he1 with ⟨g, hg, hEq⟩
        exact flux_block_disjoint_01 m f g hf hg hEq.symm

      have dj02 : B0.Disjoint B2 := by
        rw [List.disjoint_left]
        intro e he0 he2
        rcases List.mem_map.mp he0 with ⟨f, hf, rfl⟩
        rcases List.mem_map.mp he2 with ⟨g, hg, hEq⟩
        exact flux_block_disjoint_02 m f g hf hg hEq.symm

      have dj12 : B1.Disjoint B2 := by
        rw [List.disjoint_left]
        intro e he1 he2
        rcases List.mem_map.mp he1 with ⟨f, hf, rfl⟩
        rcases List.mem_map.mp he2 with ⟨g, hg, hEq⟩
        exact flux_block_disjoint_12 m f g hf hg hEq.symm

      have d12 : (B1 ++ B2).Nodup := d1.append d2 dj12
      have dj0 : B0.Disjoint (B1 ++ B2) := by
        rw [List.disjoint_left]
        intro e he0 he12
        simp only [List.mem_append] at he12
        rcases he12 with he1 | he2
        · exact (List.disjoint_left.mp dj01 he0) he1
        · exact (List.disjoint_left.mp dj02 he0) he2

      have dall : (B0 ++ (B1 ++ B2)).Nodup := d0.append d12 dj0
      simpa [fluxEdges, facesExact, Function.comp_def, B0, B1, B2] using dall
/-- The three SU(2) axes assigned cyclically to the flux edges.
The face ordering in `facesExact` is exactly the order used by the
Python reference construction, so the axis is the face position modulo 3. -/
abbrev Axis := Fin 3

def faceAxis (i : ℕ) : Axis :=
  ⟨i % 3, Nat.mod_lt _ (by omega)⟩

def axisOfFluxEdge (_m i : ℕ) : Axis :=
  faceAxis i

theorem faceAxis_zero : faceAxis 0 = 0 := by
  rfl

theorem faceAxis_one : faceAxis 1 = 1 := by
  rfl

theorem faceAxis_two : faceAxis 2 = 2 := by
  rfl

theorem faceAxis_cycle (i : ℕ) :
    faceAxis (i + 3) = faceAxis i := by
  simp [faceAxis]

/-- One full triple of faces contains one face of each axis. -/
theorem faceAxis_triple (i : ℕ) :
    faceAxis i ≠ faceAxis (i + 1) ∧
    faceAxis i ≠ faceAxis (i + 2) := by
  simp [faceAxis]
  omega

/-- The number of faces at level `m` is divisible by three for `m ≥ 1`. -/
theorem three_dvd_face_count (m : ℕ) (hm : 1 ≤ m) :
    3 ∣ (facesExact m).length := by
  rw [facesExact_length]
  induction m with
  | zero =>
      omega
  | succ m ih =>
      simp [pow_succ]

/-- The first three axis labels are exactly X, Y, Z. -/
theorem axis_cycle_first_three :
    [faceAxis 0, faceAxis 1, faceAxis 2] = [0, 1, 2] := by
  rfl

theorem faceAxis_mul_three (k : ℕ) :
    faceAxis (3 * k) = 0 := by
  apply Fin.ext
  simp [faceAxis, Nat.mul_add_mod]

theorem faceAxis_mul_three_add_one (k : ℕ) :
    faceAxis (3 * k + 1) = 1 := by
  apply Fin.ext
  simp [faceAxis, Nat.mul_add_mod]

theorem faceAxis_mul_three_add_two (k : ℕ) :
    faceAxis (3 * k + 2) = 2 := by
  apply Fin.ext
  simp [faceAxis, Nat.mul_add_mod]

end EvgenyTheorem

import EvgenyTheorem.Graph.Faces
import EvgenyTheorem.SU2
import Mathlib

namespace EvgenyTheorem

open Complex Matrix

abbrev HilbertIndex (m : ℕ) := Vertex m × C2

def axisPauli : Axis → Matrix C2 C2 ℂ
  | 0 => pauliX
  | 1 => pauliY
  | 2 => pauliZ

noncomputable def axisRotation (a : Axis) (θ : ℝ) : Matrix C2 C2 ℂ :=
  su2Rotation (axisPauli a) θ

noncomputable def fluxIndex (m : ℕ) (e : Point × Point) : ℕ :=
  (fluxEdges m).findIdx (fun f => f = e)

noncomputable def edgeAxis (m : ℕ) (e : Point × Point) : Axis :=
  faceAxis (fluxIndex m e)

noncomputable def edgeUnitary
    (m : ℕ) (θ : ℝ) (e : Point × Point) :
    Matrix C2 C2 ℂ :=
  if e ∈ fluxEdges m then
    axisRotation (edgeAxis m e) θ
  else
    (1 : Matrix C2 C2 ℂ)

noncomputable def degree (m : ℕ) (u : Vertex m) : ℕ := by
  classical
  letI : Finite (Vertex m) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (Vertex m) := Fintype.ofFinite (Vertex m)
  exact Finset.univ.sum (fun v : Vertex m => if Adj u v then 1 else 0)

noncomputable def connectionOperator
    (m : ℕ) (θ : ℝ) :
    Matrix (HilbertIndex m) (HilbertIndex m) ℂ := by
  classical
  letI : Finite (Vertex m) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (Vertex m) := Fintype.ofFinite (Vertex m)
  exact fun u v =>
    if u.1 = v.1 then
      if u.2 = v.2 then
        Complex.ofReal (degree m u.1)
      else
        0
    else if Adj u.1 v.1 then
      let pu : Point := (u.1.1.1, u.1.1.2)
      let pv : Point := (v.1.1.1, v.1.1.2)
      let e : Point × Point := if pu ≤ pv then (pu, pv) else (pv, pu)
      let U := edgeUnitary m θ e
      if pu ≤ pv then
        -U u.2 v.2
      else
        -Uᴴ u.2 v.2
    else
      0

theorem connectionOperator_diagonal
    (m : ℕ) (θ : ℝ) (u : HilbertIndex m) :
    connectionOperator m θ u u =
      Complex.ofReal (degree m u.1) := by
  classical
  simp [connectionOperator]

noncomputable def edgeUnitaryWithAxis
    (m : ℕ) (θ : ℝ) (axisOfIndex : ℕ → Axis)
    (e : Point × Point) :
    Matrix C2 C2 ℂ :=
  if e ∈ fluxEdges m then
    axisRotation (axisOfIndex (fluxIndex m e)) θ
  else
    (1 : Matrix C2 C2 ℂ)

noncomputable def connectionOperatorWithAxis
    (m : ℕ) (θ : ℝ) (axisOfIndex : ℕ → Axis) :
    Matrix (HilbertIndex m) (HilbertIndex m) ℂ := by
  classical
  letI : Finite (Vertex m) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (Vertex m) := Fintype.ofFinite (Vertex m)
  exact fun u v =>
    if u.1 = v.1 then
      if u.2 = v.2 then
        Complex.ofReal (degree m u.1)
      else
        0
    else if Adj u.1 v.1 then
      let pu : Point := (u.1.1.1, u.1.1.2)
      let pv : Point := (v.1.1.1, v.1.1.2)
      let e : Point × Point := if pu ≤ pv then (pu, pv) else (pv, pu)
      let U := edgeUnitaryWithAxis m θ axisOfIndex e
      if pu ≤ pv then
        -U u.2 v.2
      else
        -Uᴴ u.2 v.2
    else
      0

noncomputable def HC
    (m : ℕ) (θ : ℝ) :
    Matrix (HilbertIndex m) (HilbertIndex m) ℂ :=
  connectionOperatorWithAxis m θ faceAxis

noncomputable def HCprime
    (m : ℕ) (θ : ℝ) :
    Matrix (HilbertIndex m) (HilbertIndex m) ℂ :=
  connectionOperatorWithAxis m θ (fun _ => 2)

theorem connectionOperatorWithAxis_zero_eq
    (m : ℕ) (a b : ℕ → Axis) :
    connectionOperatorWithAxis m 0 a =
      connectionOperatorWithAxis m 0 b := by
  classical
  letI : Finite (Vertex m) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (Vertex m) := Fintype.ofFinite (Vertex m)
  funext u v
  simp [connectionOperatorWithAxis, edgeUnitaryWithAxis, axisRotation,
    su2Rotation]

noncomputable def traceDefect (m : ℕ) (θ : ℝ) : ℂ := by
  classical
  letI : Finite (Vertex m) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (Vertex m) := Fintype.ofFinite (Vertex m)
  letI : Finite (HilbertIndex m) := inferInstance
  letI : Fintype (HilbertIndex m) := Fintype.ofFinite (HilbertIndex m)
  exact
    Matrix.trace
        (((HC m θ * HC m θ) * HC m θ) * HC m θ) -
      Matrix.trace
        (((HCprime m θ * HCprime m θ) * HCprime m θ) * HCprime m θ)

theorem traceDefect_zero (m : ℕ) :
    traceDefect m 0 = 0 := by
  classical
  simp only [traceDefect]
  rw [show HC m 0 = HCprime m 0 from
    connectionOperatorWithAxis_zero_eq m faceAxis (fun _ => 2)]
  ring

end EvgenyTheorem


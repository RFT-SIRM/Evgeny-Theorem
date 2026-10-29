import EvgenyTheorem.FinalTilde
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

/-!
# Exact polynomial model for the finite H6 trace transition

The coefficients are Gaussian integers and the two variables are
`c = cos(θ/2)` and `s = sin(θ/2)`.  The model mirrors the entry definition
of `pHeO`: degree on the diagonal, axis-labelled SU(2) blocks on flux edges,
and the identity block on other graph edges.  The initial kernel-level target
is the exact level-two trace polynomial; the evaluation theorem that connects
this model back to `pOpO` is added separately.
-/

namespace EvgenyTheorem

open Matrix

abbrev H6Poly := MvPolynomial (Fin 2) GaussianInt

def h6PolyC : H6Poly := MvPolynomial.X 0
def h6PolyS : H6Poly := MvPolynomial.X 1
def h6PolyI : GaussianInt := ⟨0, 1⟩

/-- Forward edge block `-U` for `U = c I - i s σ_a`. -/
def h6AxisForwardEntry (a : Axis) (i j : C2) : H6Poly :=
  if a = 0 then
    if i = j then -h6PolyC else h6PolyI * h6PolyS
  else if a = 1 then
    if i = j then -h6PolyC else if i = 0 then h6PolyS else -h6PolyS
  else
    if i = j then
      if i = 0 then -h6PolyC + h6PolyI * h6PolyS
      else -h6PolyC - h6PolyI * h6PolyS
    else 0

/-- Reverse edge block `-Uᴴ`; variables are real, so only the Gaussian
coefficient is conjugated. -/
def h6AxisReverseEntry (a : Axis) (i j : C2) : H6Poly :=
  if a = 0 then
    if i = j then -h6PolyC else -(h6PolyI * h6PolyS)
  else if a = 1 then
    if i = j then -h6PolyC else if i = 0 then -h6PolyS else h6PolyS
  else
    if i = j then
      if i = 0 then -h6PolyC - h6PolyI * h6PolyS
      else -h6PolyC + h6PolyI * h6PolyS
    else 0

/-- Computable duplicate of `fluxIndex` for exact polynomial evaluation. -/
def h6FluxIndex (m : ℕ) (e : Point × Point) : ℕ :=
  (fluxEdges m).findIdx (fun f => f = e)

/-- Polynomial entry of the forward `-U` edge block; non-flux graph edges
carry `-I`, just as in the original connection operator. -/
def h6EdgeForwardEntry (m : ℕ) (ax : ℕ → Axis)
    (e : Point × Point) (i j : C2) : H6Poly :=
  if e ∈ fluxEdges m then h6AxisForwardEntry (ax (h6FluxIndex m e)) i j
  else if i = j then -1 else 0

/-- Polynomial entry of the reverse `-Uᴴ` edge block. -/
def h6EdgeReverseEntry (m : ℕ) (ax : ℕ → Axis)
    (e : Point × Point) (i j : C2) : H6Poly :=
  if e ∈ fluxEdges m then h6AxisReverseEntry (ax (h6FluxIndex m e)) i j
  else if i = j then -1 else 0

/-- Entrywise polynomial model of `pHeO`. -/
def h6PHeOPoly (m : ℕ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (p q : Point) (i j : C2) : H6Poly :=
  if p = q then
    if i = j then MvPolynomial.C ((pdeg m p : ℕ) : GaussianInt) else 0
  else if EdgeB m p.1 p.2 q.1 q.2 = true then
    let e : Point × Point := if p ≤ q then (p, q) else (q, p)
    if o p q then h6EdgeForwardEntry m ax e i j
    else h6EdgeReverseEntry m ax e i j
  else 0

/-- Polynomial model of the full point operator. -/
def h6POpOPoly (m : ℕ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] : Matrix (Pt m × C2) (Pt m × C2) H6Poly :=
  fun x y => h6PHeOPoly m ax o x.1.1 y.1.1 x.2 y.2

/-- Exact polynomial difference between the axis-cycled and commuting traces. -/
def h6DefectPoly (m : ℕ) : H6Poly :=
  Matrix.trace ((h6POpOPoly m faceAxis (oNum m)) ^ 6) -
    Matrix.trace ((h6POpOPoly m (fun _ => 2) (oNum m)) ^ 6)

/-- Raw level-two polynomial, before using the unit-circle relation
`c²+s²=1`. -/
def h6D2Raw : H6Poly :=
  -14256 * h6PolyS ^ 2 - 384 * h6PolyS ^ 3 - 336 * h6PolyS ^ 4 +
    1344 * h6PolyC * h6PolyS ^ 2 - 336 * h6PolyC ^ 2 * h6PolyS ^ 2

/-- The raw finite level-two trace calculation is exact over Gaussian
integers; no floating-point angles are involved. -/
theorem h6DefectPoly_two_raw : h6DefectPoly 2 = h6D2Raw := by
  native_decide

end EvgenyTheorem

import EvgenyTheorem.H12PolynomialGaussianExecutableRecurrence

namespace EvgenyTheorem

abbrev H12VertexSpin := Vertex 3 × C2
abbrev H12PolyGridArray := Array (Array GaussianInt)
abbrev H12AffineTriple := GaussianInt × GaussianInt × GaussianInt
abbrev H12PolySparseRows := Array (Array (Nat × H12AffineTriple))

/-- Enumerate the 42 level-three vertices in the same order used by the
materialized coefficient computation. -/
def h12VertexArray : Array (Vertex 3) :=
  ((List.ofFn fun i : Fin 81 =>
      let x := i.val / 9
      let y := i.val % 9
      if h : InSG 3 x y then
        some (⟨(⟨x, by omega⟩, ⟨y, by omega⟩),
          by simpa using h⟩ : Vertex 3)
      else none).filterMap id).toArray

/-- Each vertex is paired with both spin states. -/
def h12IndexArray : Array H12VertexSpin :=
  h12VertexArray.foldl
    (fun acc v =>
      (acc.push (v, (0 : C2))).push (v, (1 : C2))) #[]

def h12N : Nat := h12IndexArray.size

def h12IndexFn (i : Fin h12N) : H12VertexSpin :=
  h12IndexArray[i.val]'i.isLt

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem h12IndexFn_bijective :
    Function.Bijective h12IndexFn := by
  with_unfolding_all decide

noncomputable def h12IndexEquiv :
    Fin h12N ≃ H12VertexSpin :=
  Equiv.ofBijective h12IndexFn h12IndexFn_bijective

noncomputable def h12IndexEquivGaussian :
    Fin h12N ≃ H12GaussianIndex3 :=
  h12IndexEquiv.trans
    (Equiv.prodCongr (eqPt 3) (Equiv.refl C2))

/-- Trace is invariant under the exact finite-basis reindexing used by
the materialized array representation. -/
theorem h12GaussianTrace_reindex
    (M : Matrix H12GaussianIndex3 H12GaussianIndex3 GaussianInt) :
    Matrix.trace M =
      Matrix.trace
        (M.submatrix h12IndexEquivGaussian h12IndexEquivGaussian) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact
    (Equiv.sum_comp h12IndexEquivGaussian
      (fun i => M i i)).symm

def h12PolyGridZero : H12PolyGridArray :=
  Array.replicate 13 (Array.replicate 13 (0 : GaussianInt))

def h12PolyGridOne : H12PolyGridArray :=
  let row := (Array.replicate 13 (0 : GaussianInt)).set! 0 1
  (Array.replicate 13 (Array.replicate 13 (0 : GaussianInt))).set! 0 row

def h12PolyGridAdd (A B : H12PolyGridArray) : H12PolyGridArray :=
  (Array.range 13).map fun a =>
    (Array.range 13).map fun b =>
      ((A[a]!)[b]!) + ((B[a]!)[b]!)

def h12PolyGridSub (A B : H12PolyGridArray) : H12PolyGridArray :=
  (Array.range 13).map fun a =>
    (Array.range 13).map fun b =>
      ((A[a]!)[b]!) - ((B[a]!)[b]!)

def h12PolyGridGet
    (P : H12PolyGridArray) (a b : Nat) : GaussianInt :=
  ((P[a]!)[b]!)

def h12PolyGridMulAffine
    (P : H12PolyGridArray) (q : H12AffineTriple) : H12PolyGridArray :=
  let q0 : GaussianInt := q.1
  let qc : GaussianInt := q.2.1
  let qs : GaussianInt := q.2.2
  (Array.range 13).map fun a =>
    (Array.range 13).map fun b =>
      h12PolyGridGet P a b * q0 +
        (if a = 0 then (0 : GaussianInt)
         else h12PolyGridGet P (a - 1) b * qc) +
        (if b = 0 then (0 : GaussianInt)
         else h12PolyGridGet P a (b - 1) * qs)

/-- Sparse rows of the three affine coefficient matrices, indexed by the
same vertex-spin array. -/
def h12D3PolyRows (ax : ℕ → Axis) : H12PolySparseRows :=
  Array.ofFn fun i : Fin h12N =>
    let x := h12IndexArray[i.val]'i.isLt
    (Array.ofFn fun j : Fin h12N =>
      let y := h12IndexArray[j.val]'j.isLt
      let p0 := h12GaussianP0Entry
        (vpt x.1) (vpt y.1) x.2 y.2
      let pc := h12GaussianPcEntry
        (vpt x.1) (vpt y.1) x.2 y.2
      let ps := h12GaussianPsEntryFor ax (oNum 3)
        (vpt x.1) (vpt y.1) x.2 y.2
      (j.val, (p0, pc, ps))).filter fun e =>
        e.2.1 != 0 || e.2.2.1 != 0 || e.2.2.2 != 0

/-- One row-vector multiplication by the affine coefficient matrix. -/
def h12D3PolyVectorStep
    (rows : H12PolySparseRows)
    (v : Array H12PolyGridArray) : Array H12PolyGridArray :=
  Id.run do
    let mut out := Array.replicate h12N h12PolyGridZero
    for i in [:h12N] do
      let source := v[i]!
      for edge in rows[i]! do
        let j := edge.1
        let product := h12PolyGridMulAffine source edge.2
        let updated := h12PolyGridAdd out[j]! product
        out := out.set! j updated
    return out

/-- Sum the diagonal entries obtained by applying twelve affine steps to
each standard basis row. -/
def h12D3TracePolyGrid (rows : H12PolySparseRows) :
    H12PolyGridArray :=
  Id.run do
    let mut result := h12PolyGridZero
    for root in [:h12N] do
      let mut vector := Array.replicate h12N h12PolyGridZero
      vector := vector.set! root h12PolyGridOne
      for _ in [:12] do
        vector := h12D3PolyVectorStep rows vector
      result := h12PolyGridAdd result vector[root]!
    return result

def h12D3MaterializedFullGrid : H12PolyGridArray :=
  h12PolyGridSub
    (h12D3TracePolyGrid (h12D3PolyRows faceAxis))
    (h12D3TracePolyGrid (h12D3PolyRows (fun _ => 2)))

def h12D3ExpectedTerms :
    List ((Nat × Nat) × GaussianInt) :=
  [ ((0,2), ⟨-12470932128, 0⟩),
    ((0,3), ⟨285009216, 0⟩),
    ((0,4), ⟨-5089544880, 0⟩),
    ((0,5), ⟨-152326848, 0⟩),
    ((0,6), ⟨-560827936, 0⟩),
    ((0,7), ⟨-20895936, 0⟩),
    ((0,8), ⟨-16744080, 0⟩),
    ((0,9), ⟨-380352, 0⟩),
    ((0,10), ⟨-62880, 0⟩),
    ((1,2), ⟨7341160896, 0⟩),
    ((1,3), ⟨-80677152, 0⟩),
    ((1,4), ⟨1409666688, 0⟩),
    ((1,5), ⟨1289856, 0⟩),
    ((1,6), ⟨67332672, 0⟩),
    ((1,7), ⟨40320, 0⟩),
    ((1,8), ⟨739392, 0⟩),
    ((2,2), ⟨-6002023920, 0⟩),
    ((2,3), ⟨-154263936, 0⟩),
    ((2,4), ⟨-1180398528, 0⟩),
    ((2,5), ⟨-42014592, 0⟩),
    ((2,6), ⟨-50563152, 0⟩),
    ((2,7), ⟨-1141056, 0⟩),
    ((2,8), ⟨-251520, 0⟩),
    ((3,2), ⟨1484289984, 0⟩),
    ((3,3), ⟨2647680, 0⟩),
    ((3,4), ⟨136851072, 0⟩),
    ((3,5), ⟨95424, 0⟩),
    ((3,6), ⟨2218176, 0⟩),
    ((4,2), ⟨-622111776, 0⟩),
    ((4,3), ⟨-21183936, 0⟩),
    ((4,4), ⟨-50916720, 0⟩),
    ((4,5), ⟨-1141056, 0⟩),
    ((4,6), ⟨-377280, 0⟩),
    ((5,2), ⟨69551424, 0⟩),
    ((5,3), ⟨55872, 0⟩),
    ((5,4), ⟨2218176, 0⟩),
    ((6,2), ⟨-17098032, 0⟩),
    ((6,3), ⟨-380352, 0⟩),
    ((6,4), ⟨-251520, 0⟩),
    ((7,2), ⟨739392, 0⟩),
    ((8,2), ⟨-62880, 0⟩) ]

def h12D3ExpectedFullGrid : H12PolyGridArray :=
  h12D3ExpectedTerms.foldl
    (fun grid term =>
      let a := term.1.1
      let b := term.1.2
      grid.set! a ((grid[a]!).set! b term.2))
    h12PolyGridZero

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem h12ListArray_ext {α : Type}
    {xs ys : List (Array α)}
    (h : xs.map Array.toList = ys.map Array.toList) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => cases h
  | cons x xs ih =>
      cases ys with
      | nil => cases h
      | cons y ys =>
          simp only [List.map_cons] at h
          injection h with hxy htail
          have hxy' : x = y := Array.ext' hxy
          have htail' : xs = ys := ih htail
          simp [hxy', htail']

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem h12D3MaterializedFullGrid_eq_expected :
    h12D3MaterializedFullGrid = h12D3ExpectedFullGrid := by
  apply Array.ext'
  apply h12ListArray_ext
  change
    (h12D3MaterializedFullGrid.toList.map Array.toList) =
      (h12D3ExpectedFullGrid.toList.map Array.toList)
  with_unfolding_all decide

/-- The c⁰s² cell of the full-grid calculation agrees with the independently
proved Gaussian executable coefficient recurrence. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem h12D3GridS2_eq_executable :
    h12PolyGridGet h12D3MaterializedFullGrid 0 2 =
      h12GaussianD3S2CoefficientExec := by
  with_unfolding_all decide

#print axioms h12IndexFn_bijective
#print axioms h12GaussianTrace_reindex
#print axioms h12D3MaterializedFullGrid_eq_expected
#print axioms h12D3GridS2_eq_executable

end EvgenyTheorem

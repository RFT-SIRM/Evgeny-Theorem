import EvgenyTheorem.TraceExpand

namespace EvgenyTheorem

/-! ## Finite cyclic-orbit inventory for the degree-12 expansion

This module turns the independently enumerated positive compositions
into kernel-checked finite orbit partitions. It is combinatorial input
for the H12 trace-stratum reductions; it is not itself the operator
recurrence. -/

@[instance_reducible]
private def binaryWordP12GapVectorFintypeComputable (r : ℕ) :
    Fintype (binaryWordGapVectorStratum 12 r) := by
  unfold binaryWordGapVectorStratum
  let P : (Fin r → Fin (12 - r + 1)) → Prop := fun v =>
    r ≤ 12 ∧ (List.ofFn (fun i : Fin r => (v i).val)).sum = 12 - r
  letI : DecidablePred P := fun v => inferInstance
  refine Fintype.subtype (Finset.univ.filter P) ?_
  intro v
  simp [P]

private def binaryWordP12PositiveGapListFinsetOfFintype (r : ℕ)
    (inst : Fintype (binaryWordGapVectorStratum 12 r)) : Finset (List ℕ) :=
  (@Finset.univ (binaryWordGapVectorStratum 12 r) inst).image
    (fun gaps =>
      (List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ)

noncomputable def binaryWordP12PositiveGapListFinset (r : ℕ) :
    Finset (List ℕ) :=
  binaryWordP12PositiveGapListFinsetOfFintype r
    (binaryWordGapVectorStratum_fintype 12 r)

private def binaryWordP12PositiveGapListFinsetComputable (r : ℕ) :
    Finset (List ℕ) :=
  binaryWordP12PositiveGapListFinsetOfFintype r
    (binaryWordP12GapVectorFintypeComputable r)

private theorem binaryWordP12PositiveGapListFinset_eq_computable (r : ℕ) :
    binaryWordP12PositiveGapListFinset r =
      binaryWordP12PositiveGapListFinsetComputable r := by
  exact congrArg (binaryWordP12PositiveGapListFinsetOfFintype r)
    (Subsingleton.elim _ _)

private def binaryWordP12GapOrbitPairwiseCheck (reps : List (List ℕ)) : Bool :=
  reps.all (fun a =>
    reps.all (fun b =>
      decide (a = b) ||
        decide (cyclicGapOrbit a ∩ cyclicGapOrbit b = ∅)))

private theorem binaryWordP12PairwiseDisjoint_of_check
    (reps : List (List ℕ))
    (hcheck : binaryWordP12GapOrbitPairwiseCheck reps = true) :
    Set.PairwiseDisjoint (↑reps.toFinset) cyclicGapOrbit := by
  classical
  intro a ha b hb hab
  change Disjoint (cyclicGapOrbit a) (cyclicGapOrbit b)
  have haList : a ∈ reps := by simpa using ha
  have hbList : b ∈ reps := by simpa using hb
  have houter := (List.all_eq_true.mp hcheck) a haList
  have hinner := (List.all_eq_true.mp houter) b hbList
  have hdisjBool :
      decide (cyclicGapOrbit a ∩ cyclicGapOrbit b = ∅) = true := by
    simpa [hab] using hinner
  have hempty : cyclicGapOrbit a ∩ cyclicGapOrbit b = ∅ :=
    of_decide_eq_true hdisjBool
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  have hx : x ∈ cyclicGapOrbit a ∩ cyclicGapOrbit b :=
    Finset.mem_inter.mpr ⟨hxa, hxb⟩
  rw [hempty] at hx
  simpa using hx


/-- Ordered canonical representatives for the p=12 r=2 stratum. -/
private def binaryWordP12GapOrbitRepList2 : List (List ℕ) :=
  [[1, 11],
  [2, 10],
  [3, 9],
  [4, 8],
  [5, 7],
  [6, 6]]

/-- Canonical p=12 cyclic representatives for the r=2 stratum. -/
def binaryWordP12GapOrbitReps2 : Finset (List ℕ) :=
  binaryWordP12GapOrbitRepList2.toFinset


/-- Ordered canonical representatives for the p=12 r=4 stratum. -/
private def binaryWordP12GapOrbitRepList4 : List (List ℕ) :=
  [[1, 1, 1, 9],
  [1, 1, 2, 8],
  [1, 1, 3, 7],
  [1, 1, 4, 6],
  [1, 1, 5, 5],
  [1, 1, 6, 4],
  [1, 1, 7, 3],
  [1, 1, 8, 2],
  [1, 2, 1, 8],
  [1, 2, 2, 7],
  [1, 2, 3, 6],
  [1, 2, 4, 5],
  [1, 2, 5, 4],
  [1, 2, 6, 3],
  [1, 2, 7, 2],
  [1, 3, 1, 7],
  [1, 3, 2, 6],
  [1, 3, 3, 5],
  [1, 3, 4, 4],
  [1, 3, 5, 3],
  [1, 3, 6, 2],
  [1, 4, 1, 6],
  [1, 4, 2, 5],
  [1, 4, 3, 4],
  [1, 4, 4, 3],
  [1, 4, 5, 2],
  [1, 5, 1, 5],
  [1, 5, 2, 4],
  [1, 5, 3, 3],
  [1, 5, 4, 2],
  [1, 6, 2, 3],
  [1, 6, 3, 2],
  [1, 7, 2, 2],
  [2, 2, 2, 6],
  [2, 2, 3, 5],
  [2, 2, 4, 4],
  [2, 2, 5, 3],
  [2, 3, 2, 5],
  [2, 3, 3, 4],
  [2, 3, 4, 3],
  [2, 4, 2, 4],
  [2, 4, 3, 3],
  [3, 3, 3, 3]]

/-- Canonical p=12 cyclic representatives for the r=4 stratum. -/
def binaryWordP12GapOrbitReps4 : Finset (List ℕ) :=
  binaryWordP12GapOrbitRepList4.toFinset


/-- Ordered canonical representatives for the p=12 r=6 stratum. -/
private def binaryWordP12GapOrbitRepList6 : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 7],
  [1, 1, 1, 1, 2, 6],
  [1, 1, 1, 1, 3, 5],
  [1, 1, 1, 1, 4, 4],
  [1, 1, 1, 1, 5, 3],
  [1, 1, 1, 1, 6, 2],
  [1, 1, 1, 2, 1, 6],
  [1, 1, 1, 2, 2, 5],
  [1, 1, 1, 2, 3, 4],
  [1, 1, 1, 2, 4, 3],
  [1, 1, 1, 2, 5, 2],
  [1, 1, 1, 3, 1, 5],
  [1, 1, 1, 3, 2, 4],
  [1, 1, 1, 3, 3, 3],
  [1, 1, 1, 3, 4, 2],
  [1, 1, 1, 4, 1, 4],
  [1, 1, 1, 4, 2, 3],
  [1, 1, 1, 4, 3, 2],
  [1, 1, 1, 5, 1, 3],
  [1, 1, 1, 5, 2, 2],
  [1, 1, 1, 6, 1, 2],
  [1, 1, 2, 1, 1, 6],
  [1, 1, 2, 1, 2, 5],
  [1, 1, 2, 1, 3, 4],
  [1, 1, 2, 1, 4, 3],
  [1, 1, 2, 1, 5, 2],
  [1, 1, 2, 2, 1, 5],
  [1, 1, 2, 2, 2, 4],
  [1, 1, 2, 2, 3, 3],
  [1, 1, 2, 2, 4, 2],
  [1, 1, 2, 3, 1, 4],
  [1, 1, 2, 3, 2, 3],
  [1, 1, 2, 3, 3, 2],
  [1, 1, 2, 4, 1, 3],
  [1, 1, 2, 4, 2, 2],
  [1, 1, 2, 5, 1, 2],
  [1, 1, 3, 1, 1, 5],
  [1, 1, 3, 1, 2, 4],
  [1, 1, 3, 1, 3, 3],
  [1, 1, 3, 1, 4, 2],
  [1, 1, 3, 2, 1, 4],
  [1, 1, 3, 2, 2, 3],
  [1, 1, 3, 2, 3, 2],
  [1, 1, 3, 3, 1, 3],
  [1, 1, 3, 3, 2, 2],
  [1, 1, 3, 4, 1, 2],
  [1, 1, 4, 1, 1, 4],
  [1, 1, 4, 1, 2, 3],
  [1, 1, 4, 1, 3, 2],
  [1, 1, 4, 2, 1, 3],
  [1, 1, 4, 2, 2, 2],
  [1, 1, 4, 3, 1, 2],
  [1, 1, 5, 1, 2, 2],
  [1, 1, 5, 2, 1, 2],
  [1, 2, 1, 2, 1, 5],
  [1, 2, 1, 2, 2, 4],
  [1, 2, 1, 2, 3, 3],
  [1, 2, 1, 2, 4, 2],
  [1, 2, 1, 3, 1, 4],
  [1, 2, 1, 3, 2, 3],
  [1, 2, 1, 3, 3, 2],
  [1, 2, 1, 4, 1, 3],
  [1, 2, 1, 4, 2, 2],
  [1, 2, 2, 1, 2, 4],
  [1, 2, 2, 1, 3, 3],
  [1, 2, 2, 1, 4, 2],
  [1, 2, 2, 2, 1, 4],
  [1, 2, 2, 2, 2, 3],
  [1, 2, 2, 2, 3, 2],
  [1, 2, 2, 3, 1, 3],
  [1, 2, 2, 3, 2, 2],
  [1, 2, 3, 1, 2, 3],
  [1, 2, 3, 1, 3, 2],
  [1, 2, 3, 2, 1, 3],
  [1, 2, 3, 2, 2, 2],
  [1, 3, 1, 3, 1, 3],
  [1, 3, 1, 3, 2, 2],
  [1, 3, 2, 1, 3, 2],
  [1, 3, 2, 2, 2, 2],
  [2, 2, 2, 2, 2, 2]]

/-- Canonical p=12 cyclic representatives for the r=6 stratum. -/
def binaryWordP12GapOrbitReps6 : Finset (List ℕ) :=
  binaryWordP12GapOrbitRepList6.toFinset


/-- Ordered canonical representatives for the p=12 r=8 stratum. -/
private def binaryWordP12GapOrbitRepList8 : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 1, 1, 5],
  [1, 1, 1, 1, 1, 1, 2, 4],
  [1, 1, 1, 1, 1, 1, 3, 3],
  [1, 1, 1, 1, 1, 1, 4, 2],
  [1, 1, 1, 1, 1, 2, 1, 4],
  [1, 1, 1, 1, 1, 2, 2, 3],
  [1, 1, 1, 1, 1, 2, 3, 2],
  [1, 1, 1, 1, 1, 3, 1, 3],
  [1, 1, 1, 1, 1, 3, 2, 2],
  [1, 1, 1, 1, 1, 4, 1, 2],
  [1, 1, 1, 1, 2, 1, 1, 4],
  [1, 1, 1, 1, 2, 1, 2, 3],
  [1, 1, 1, 1, 2, 1, 3, 2],
  [1, 1, 1, 1, 2, 2, 1, 3],
  [1, 1, 1, 1, 2, 2, 2, 2],
  [1, 1, 1, 1, 2, 3, 1, 2],
  [1, 1, 1, 1, 3, 1, 1, 3],
  [1, 1, 1, 1, 3, 1, 2, 2],
  [1, 1, 1, 1, 3, 2, 1, 2],
  [1, 1, 1, 1, 4, 1, 1, 2],
  [1, 1, 1, 2, 1, 1, 1, 4],
  [1, 1, 1, 2, 1, 1, 2, 3],
  [1, 1, 1, 2, 1, 1, 3, 2],
  [1, 1, 1, 2, 1, 2, 1, 3],
  [1, 1, 1, 2, 1, 2, 2, 2],
  [1, 1, 1, 2, 1, 3, 1, 2],
  [1, 1, 1, 2, 2, 1, 1, 3],
  [1, 1, 1, 2, 2, 1, 2, 2],
  [1, 1, 1, 2, 2, 2, 1, 2],
  [1, 1, 1, 2, 3, 1, 1, 2],
  [1, 1, 1, 3, 1, 1, 1, 3],
  [1, 1, 1, 3, 1, 1, 2, 2],
  [1, 1, 1, 3, 1, 2, 1, 2],
  [1, 1, 1, 3, 2, 1, 1, 2],
  [1, 1, 2, 1, 1, 2, 1, 3],
  [1, 1, 2, 1, 1, 2, 2, 2],
  [1, 1, 2, 1, 1, 3, 1, 2],
  [1, 1, 2, 1, 2, 1, 1, 3],
  [1, 1, 2, 1, 2, 1, 2, 2],
  [1, 1, 2, 1, 2, 2, 1, 2],
  [1, 1, 2, 2, 1, 1, 2, 2],
  [1, 1, 2, 2, 1, 2, 1, 2],
  [1, 2, 1, 2, 1, 2, 1, 2]]

/-- Canonical p=12 cyclic representatives for the r=8 stratum. -/
def binaryWordP12GapOrbitReps8 : Finset (List ℕ) :=
  binaryWordP12GapOrbitRepList8.toFinset


/-- Ordered canonical representatives for the p=12 r=10 stratum. -/
private def binaryWordP12GapOrbitRepList10 : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1, 3],
  [1, 1, 1, 1, 1, 1, 1, 1, 2, 2],
  [1, 1, 1, 1, 1, 1, 1, 2, 1, 2],
  [1, 1, 1, 1, 1, 1, 2, 1, 1, 2],
  [1, 1, 1, 1, 1, 2, 1, 1, 1, 2],
  [1, 1, 1, 1, 2, 1, 1, 1, 1, 2]]

/-- Canonical p=12 cyclic representatives for the r=10 stratum. -/
def binaryWordP12GapOrbitReps10 : Finset (List ℕ) :=
  binaryWordP12GapOrbitRepList10.toFinset


/-- Ordered canonical representatives for the p=12 r=12 stratum. -/
private def binaryWordP12GapOrbitRepList12 : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

/-- Canonical p=12 cyclic representatives for the r=12 stratum. -/
def binaryWordP12GapOrbitReps12 : Finset (List ℕ) :=
  binaryWordP12GapOrbitRepList12.toFinset


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite verification of the p=12, r=2 orbit partition. -/
private theorem binaryWordP12GapOrbitPartitionComputable2 :
    binaryWordP12PositiveGapListFinsetComputable 2 =
      binaryWordP12GapOrbitReps2.biUnion cyclicGapOrbit := by
  native_decide

/-- The p=12 positive compositions with r=2 parts are exactly
the union of the listed disjoint cyclic orbits (6 classes). -/
theorem binaryWordP12GapOrbitPartition2 :
    binaryWordP12PositiveGapListFinset 2 =
      binaryWordP12GapOrbitReps2.biUnion cyclicGapOrbit := by
  rw [binaryWordP12PositiveGapListFinset_eq_computable]
  exact binaryWordP12GapOrbitPartitionComputable2


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite check of all pairwise orbit intersections for r=2. -/
private theorem binaryWordP12GapOrbitPairwiseCheck2 :
    binaryWordP12GapOrbitPairwiseCheck binaryWordP12GapOrbitRepList2 = true := by
  native_decide

/-- The p=12 r=2 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP12GapOrbitReps2_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP12GapOrbitReps2) cyclicGapOrbit := by
  simpa [binaryWordP12GapOrbitReps2] using
    binaryWordP12PairwiseDisjoint_of_check
      binaryWordP12GapOrbitRepList2
      binaryWordP12GapOrbitPairwiseCheck2


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite verification of the p=12, r=4 orbit partition. -/
private theorem binaryWordP12GapOrbitPartitionComputable4 :
    binaryWordP12PositiveGapListFinsetComputable 4 =
      binaryWordP12GapOrbitReps4.biUnion cyclicGapOrbit := by
  native_decide

/-- The p=12 positive compositions with r=4 parts are exactly
the union of the listed disjoint cyclic orbits (43 classes). -/
theorem binaryWordP12GapOrbitPartition4 :
    binaryWordP12PositiveGapListFinset 4 =
      binaryWordP12GapOrbitReps4.biUnion cyclicGapOrbit := by
  rw [binaryWordP12PositiveGapListFinset_eq_computable]
  exact binaryWordP12GapOrbitPartitionComputable4


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite check of all pairwise orbit intersections for r=4. -/
private theorem binaryWordP12GapOrbitPairwiseCheck4 :
    binaryWordP12GapOrbitPairwiseCheck binaryWordP12GapOrbitRepList4 = true := by
  native_decide

/-- The p=12 r=4 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP12GapOrbitReps4_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP12GapOrbitReps4) cyclicGapOrbit := by
  simpa [binaryWordP12GapOrbitReps4] using
    binaryWordP12PairwiseDisjoint_of_check
      binaryWordP12GapOrbitRepList4
      binaryWordP12GapOrbitPairwiseCheck4


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite verification of the p=12, r=6 orbit partition. -/
private theorem binaryWordP12GapOrbitPartitionComputable6 :
    binaryWordP12PositiveGapListFinsetComputable 6 =
      binaryWordP12GapOrbitReps6.biUnion cyclicGapOrbit := by
  native_decide

/-- The p=12 positive compositions with r=6 parts are exactly
the union of the listed disjoint cyclic orbits (80 classes). -/
theorem binaryWordP12GapOrbitPartition6 :
    binaryWordP12PositiveGapListFinset 6 =
      binaryWordP12GapOrbitReps6.biUnion cyclicGapOrbit := by
  rw [binaryWordP12PositiveGapListFinset_eq_computable]
  exact binaryWordP12GapOrbitPartitionComputable6


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite check of all pairwise orbit intersections for r=6. -/
private theorem binaryWordP12GapOrbitPairwiseCheck6 :
    binaryWordP12GapOrbitPairwiseCheck binaryWordP12GapOrbitRepList6 = true := by
  native_decide

/-- The p=12 r=6 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP12GapOrbitReps6_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP12GapOrbitReps6) cyclicGapOrbit := by
  simpa [binaryWordP12GapOrbitReps6] using
    binaryWordP12PairwiseDisjoint_of_check
      binaryWordP12GapOrbitRepList6
      binaryWordP12GapOrbitPairwiseCheck6


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite verification of the p=12, r=8 orbit partition. -/
private theorem binaryWordP12GapOrbitPartitionComputable8 :
    binaryWordP12PositiveGapListFinsetComputable 8 =
      binaryWordP12GapOrbitReps8.biUnion cyclicGapOrbit := by
  native_decide

/-- The p=12 positive compositions with r=8 parts are exactly
the union of the listed disjoint cyclic orbits (43 classes). -/
theorem binaryWordP12GapOrbitPartition8 :
    binaryWordP12PositiveGapListFinset 8 =
      binaryWordP12GapOrbitReps8.biUnion cyclicGapOrbit := by
  rw [binaryWordP12PositiveGapListFinset_eq_computable]
  exact binaryWordP12GapOrbitPartitionComputable8


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite check of all pairwise orbit intersections for r=8. -/
private theorem binaryWordP12GapOrbitPairwiseCheck8 :
    binaryWordP12GapOrbitPairwiseCheck binaryWordP12GapOrbitRepList8 = true := by
  native_decide

/-- The p=12 r=8 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP12GapOrbitReps8_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP12GapOrbitReps8) cyclicGapOrbit := by
  simpa [binaryWordP12GapOrbitReps8] using
    binaryWordP12PairwiseDisjoint_of_check
      binaryWordP12GapOrbitRepList8
      binaryWordP12GapOrbitPairwiseCheck8


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite verification of the p=12, r=10 orbit partition. -/
private theorem binaryWordP12GapOrbitPartitionComputable10 :
    binaryWordP12PositiveGapListFinsetComputable 10 =
      binaryWordP12GapOrbitReps10.biUnion cyclicGapOrbit := by
  native_decide

/-- The p=12 positive compositions with r=10 parts are exactly
the union of the listed disjoint cyclic orbits (6 classes). -/
theorem binaryWordP12GapOrbitPartition10 :
    binaryWordP12PositiveGapListFinset 10 =
      binaryWordP12GapOrbitReps10.biUnion cyclicGapOrbit := by
  rw [binaryWordP12PositiveGapListFinset_eq_computable]
  exact binaryWordP12GapOrbitPartitionComputable10


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite check of all pairwise orbit intersections for r=10. -/
private theorem binaryWordP12GapOrbitPairwiseCheck10 :
    binaryWordP12GapOrbitPairwiseCheck binaryWordP12GapOrbitRepList10 = true := by
  native_decide

/-- The p=12 r=10 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP12GapOrbitReps10_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP12GapOrbitReps10) cyclicGapOrbit := by
  simpa [binaryWordP12GapOrbitReps10] using
    binaryWordP12PairwiseDisjoint_of_check
      binaryWordP12GapOrbitRepList10
      binaryWordP12GapOrbitPairwiseCheck10


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite verification of the p=12, r=12 orbit partition. -/
private theorem binaryWordP12GapOrbitPartitionComputable12 :
    binaryWordP12PositiveGapListFinsetComputable 12 =
      binaryWordP12GapOrbitReps12.biUnion cyclicGapOrbit := by
  native_decide

/-- The p=12 positive compositions with r=12 parts are exactly
the union of the listed disjoint cyclic orbits (1 classes). -/
theorem binaryWordP12GapOrbitPartition12 :
    binaryWordP12PositiveGapListFinset 12 =
      binaryWordP12GapOrbitReps12.biUnion cyclicGapOrbit := by
  rw [binaryWordP12PositiveGapListFinset_eq_computable]
  exact binaryWordP12GapOrbitPartitionComputable12


set_option maxRecDepth 32768 in
set_option maxHeartbeats 160000000 in
/-- Computed finite check of all pairwise orbit intersections for r=12. -/
private theorem binaryWordP12GapOrbitPairwiseCheck12 :
    binaryWordP12GapOrbitPairwiseCheck binaryWordP12GapOrbitRepList12 = true := by
  native_decide

/-- The p=12 r=12 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP12GapOrbitReps12_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP12GapOrbitReps12) cyclicGapOrbit := by
  simpa [binaryWordP12GapOrbitReps12] using
    binaryWordP12PairwiseDisjoint_of_check
      binaryWordP12GapOrbitRepList12
      binaryWordP12GapOrbitPairwiseCheck12


/-- Reindex the p=12 positive-gap list by its nonnegative gap vectors. -/
theorem binaryWordP12PositiveGapListFinset_sum_eq_gapVector_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (r : ℕ) :
    (∑ gaps ∈ binaryWordP12PositiveGapListFinset r,
      cyclicGapTrace K N gaps) =
    ∑ gaps : binaryWordGapVectorStratum 12 r,
      cyclicGapTrace K N
        ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ) := by
  classical
  let positiveList : binaryWordGapVectorStratum 12 r → List ℕ :=
    fun gaps =>
      (List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ
  have hpositiveList_injective : Function.Injective positiveList := by
    intro a b hab
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hlist :
        List.ofFn (fun i : Fin r => (a.val i).val) =
          List.ofFn (fun i : Fin r => (b.val i).val) :=
      (List.map_inj_right (fun x y hxy => Nat.succ.inj hxy)).mp hab
    have hfun :
        (fun i : Fin r => (a.val i).val) =
          (fun i : Fin r => (b.val i).val) :=
      List.ofFn_injective hlist
    exact congrFun hfun i
  change
    (∑ gaps ∈
      (Finset.univ : Finset (binaryWordGapVectorStratum 12 r)).image positiveList,
      cyclicGapTrace K N gaps) =
    ∑ gaps : binaryWordGapVectorStratum 12 r,
      cyclicGapTrace K N (positiveList gaps)
  rw [Finset.sum_image (fun a _ b _ h => hpositiveList_injective h)]


/-- Normalize the p=12 marked-word/cyclic-gap identity by the number r
of selected letters. -/
private theorem binaryWordP12_normalize_weighted_orbit_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (r : ℕ) (hr : r ≠ 0)
    (reps : Finset (List ℕ)) (W : ℂ)
    (h : (r : ℂ) * W =
      (12 : ℂ) *
        ∑ rep ∈ reps,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep) :
    W =
      ∑ rep ∈ reps,
        ((12 : ℂ) / (r : ℂ)) *
          ((cyclicGapOrbit rep).card : ℂ) *
          cyclicGapTrace K N rep := by
  have hrC : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr
  have hdiv :
      W = ((12 : ℂ) / (r : ℂ)) *
        (∑ rep ∈ reps,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep) := by
    calc
      W = ((r : ℂ) * W) / (r : ℂ) := by
        field_simp [hrC]
      _ = ((12 : ℂ) *
          ∑ rep ∈ reps,
            (cyclicGapOrbit rep).card • cyclicGapTrace K N rep) /
          (r : ℂ) := by rw [h]
      _ = ((12 : ℂ) / (r : ℂ)) *
          (∑ rep ∈ reps,
            (cyclicGapOrbit rep).card • cyclicGapTrace K N rep) := by
        ring
  calc
    W = ((12 : ℂ) / (r : ℂ)) *
        (∑ rep ∈ reps,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep) := hdiv
    _ = ∑ rep ∈ reps,
        ((12 : ℂ) / (r : ℂ)) *
          ((cyclicGapOrbit rep).card : ℂ) *
          cyclicGapTrace K N rep := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rep hrep
      simp only [nsmul_eq_mul]
      ring


/-- Exact orbit-sum decomposition of the p=12, r=2 positive-gap
stratum. Orbit sizes count periodic representatives with their true
multiplicity. -/
theorem binaryWordP12GapTraceOrbitSum2
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP12PositiveGapListFinset 2,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP12GapOrbitReps2,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP12GapOrbitPartition2]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP12GapOrbitReps2_pairwise_disjoint


/-- The exact-count p=12, r=2 word trace sum, normalized by the
number of marked true positions, equals the cyclic positive-gap
orbit sum with exact periodic-orbit multiplicities. -/
theorem binaryWordP12WordTraceOrbitSum2
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (2 : ℂ) *
      ∑ w : binaryWordFinStratum 12 2,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (12 : ℂ) *
      ∑ rep ∈ binaryWordP12GapOrbitReps2,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (12 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 12 2,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 2 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 12 2
    _ = (12 : ℂ) *
        ∑ gaps ∈ binaryWordP12PositiveGapListFinset 2,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP12PositiveGapListFinset_sum_eq_gapVector_sum K N 2]
    _ = (12 : ℂ) *
        ∑ rep ∈ binaryWordP12GapOrbitReps2,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP12GapTraceOrbitSum2 K N]


/-- Normalized p=12, r=2 word stratum in its exact cyclic classes. -/
theorem binaryWordP12WordTraceOrbitAverage2
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 12 2,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP12GapOrbitReps2,
      ((12 : ℂ) / (2 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) * cyclicGapTrace K N rep := by
  apply binaryWordP12_normalize_weighted_orbit_sum K N 2 (by norm_num)
    binaryWordP12GapOrbitReps2
  exact binaryWordP12WordTraceOrbitSum2 K N


/-- Exact orbit-sum decomposition of the p=12, r=4 positive-gap
stratum. Orbit sizes count periodic representatives with their true
multiplicity. -/
theorem binaryWordP12GapTraceOrbitSum4
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP12PositiveGapListFinset 4,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP12GapOrbitReps4,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP12GapOrbitPartition4]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP12GapOrbitReps4_pairwise_disjoint


/-- The exact-count p=12, r=4 word trace sum, normalized by the
number of marked true positions, equals the cyclic positive-gap
orbit sum with exact periodic-orbit multiplicities. -/
theorem binaryWordP12WordTraceOrbitSum4
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (4 : ℂ) *
      ∑ w : binaryWordFinStratum 12 4,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (12 : ℂ) *
      ∑ rep ∈ binaryWordP12GapOrbitReps4,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (12 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 12 4,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 4 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 12 4
    _ = (12 : ℂ) *
        ∑ gaps ∈ binaryWordP12PositiveGapListFinset 4,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP12PositiveGapListFinset_sum_eq_gapVector_sum K N 4]
    _ = (12 : ℂ) *
        ∑ rep ∈ binaryWordP12GapOrbitReps4,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP12GapTraceOrbitSum4 K N]


/-- Normalized p=12, r=4 word stratum in its exact cyclic classes. -/
theorem binaryWordP12WordTraceOrbitAverage4
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 12 4,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP12GapOrbitReps4,
      ((12 : ℂ) / (4 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) * cyclicGapTrace K N rep := by
  apply binaryWordP12_normalize_weighted_orbit_sum K N 4 (by norm_num)
    binaryWordP12GapOrbitReps4
  exact binaryWordP12WordTraceOrbitSum4 K N


/-- Exact orbit-sum decomposition of the p=12, r=6 positive-gap
stratum. Orbit sizes count periodic representatives with their true
multiplicity. -/
theorem binaryWordP12GapTraceOrbitSum6
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP12PositiveGapListFinset 6,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP12GapOrbitReps6,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP12GapOrbitPartition6]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP12GapOrbitReps6_pairwise_disjoint


/-- The exact-count p=12, r=6 word trace sum, normalized by the
number of marked true positions, equals the cyclic positive-gap
orbit sum with exact periodic-orbit multiplicities. -/
theorem binaryWordP12WordTraceOrbitSum6
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (6 : ℂ) *
      ∑ w : binaryWordFinStratum 12 6,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (12 : ℂ) *
      ∑ rep ∈ binaryWordP12GapOrbitReps6,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (12 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 12 6,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 6 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 12 6
    _ = (12 : ℂ) *
        ∑ gaps ∈ binaryWordP12PositiveGapListFinset 6,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP12PositiveGapListFinset_sum_eq_gapVector_sum K N 6]
    _ = (12 : ℂ) *
        ∑ rep ∈ binaryWordP12GapOrbitReps6,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP12GapTraceOrbitSum6 K N]


/-- Normalized p=12, r=6 word stratum in its exact cyclic classes. -/
theorem binaryWordP12WordTraceOrbitAverage6
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 12 6,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP12GapOrbitReps6,
      ((12 : ℂ) / (6 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) * cyclicGapTrace K N rep := by
  apply binaryWordP12_normalize_weighted_orbit_sum K N 6 (by norm_num)
    binaryWordP12GapOrbitReps6
  exact binaryWordP12WordTraceOrbitSum6 K N


/-- Exact orbit-sum decomposition of the p=12, r=8 positive-gap
stratum. Orbit sizes count periodic representatives with their true
multiplicity. -/
theorem binaryWordP12GapTraceOrbitSum8
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP12PositiveGapListFinset 8,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP12GapOrbitReps8,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP12GapOrbitPartition8]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP12GapOrbitReps8_pairwise_disjoint


/-- The exact-count p=12, r=8 word trace sum, normalized by the
number of marked true positions, equals the cyclic positive-gap
orbit sum with exact periodic-orbit multiplicities. -/
theorem binaryWordP12WordTraceOrbitSum8
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (8 : ℂ) *
      ∑ w : binaryWordFinStratum 12 8,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (12 : ℂ) *
      ∑ rep ∈ binaryWordP12GapOrbitReps8,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (12 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 12 8,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 8 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 12 8
    _ = (12 : ℂ) *
        ∑ gaps ∈ binaryWordP12PositiveGapListFinset 8,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP12PositiveGapListFinset_sum_eq_gapVector_sum K N 8]
    _ = (12 : ℂ) *
        ∑ rep ∈ binaryWordP12GapOrbitReps8,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP12GapTraceOrbitSum8 K N]


/-- Normalized p=12, r=8 word stratum in its exact cyclic classes. -/
theorem binaryWordP12WordTraceOrbitAverage8
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 12 8,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP12GapOrbitReps8,
      ((12 : ℂ) / (8 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) * cyclicGapTrace K N rep := by
  apply binaryWordP12_normalize_weighted_orbit_sum K N 8 (by norm_num)
    binaryWordP12GapOrbitReps8
  exact binaryWordP12WordTraceOrbitSum8 K N


/-- Exact orbit-sum decomposition of the p=12, r=10 positive-gap
stratum. Orbit sizes count periodic representatives with their true
multiplicity. -/
theorem binaryWordP12GapTraceOrbitSum10
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP12PositiveGapListFinset 10,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP12GapOrbitReps10,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP12GapOrbitPartition10]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP12GapOrbitReps10_pairwise_disjoint


/-- The exact-count p=12, r=10 word trace sum, normalized by the
number of marked true positions, equals the cyclic positive-gap
orbit sum with exact periodic-orbit multiplicities. -/
theorem binaryWordP12WordTraceOrbitSum10
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (10 : ℂ) *
      ∑ w : binaryWordFinStratum 12 10,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (12 : ℂ) *
      ∑ rep ∈ binaryWordP12GapOrbitReps10,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (12 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 12 10,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 10 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 12 10
    _ = (12 : ℂ) *
        ∑ gaps ∈ binaryWordP12PositiveGapListFinset 10,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP12PositiveGapListFinset_sum_eq_gapVector_sum K N 10]
    _ = (12 : ℂ) *
        ∑ rep ∈ binaryWordP12GapOrbitReps10,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP12GapTraceOrbitSum10 K N]


/-- Normalized p=12, r=10 word stratum in its exact cyclic classes. -/
theorem binaryWordP12WordTraceOrbitAverage10
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 12 10,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP12GapOrbitReps10,
      ((12 : ℂ) / (10 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) * cyclicGapTrace K N rep := by
  apply binaryWordP12_normalize_weighted_orbit_sum K N 10 (by norm_num)
    binaryWordP12GapOrbitReps10
  exact binaryWordP12WordTraceOrbitSum10 K N


/-- Exact orbit-sum decomposition of the p=12, r=12 positive-gap
stratum. Orbit sizes count periodic representatives with their true
multiplicity. -/
theorem binaryWordP12GapTraceOrbitSum12
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP12PositiveGapListFinset 12,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP12GapOrbitReps12,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP12GapOrbitPartition12]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP12GapOrbitReps12_pairwise_disjoint


/-- The exact-count p=12, r=12 word trace sum, normalized by the
number of marked true positions, equals the cyclic positive-gap
orbit sum with exact periodic-orbit multiplicities. -/
theorem binaryWordP12WordTraceOrbitSum12
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (12 : ℂ) *
      ∑ w : binaryWordFinStratum 12 12,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (12 : ℂ) *
      ∑ rep ∈ binaryWordP12GapOrbitReps12,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (12 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 12 12,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 12 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 12 12
    _ = (12 : ℂ) *
        ∑ gaps ∈ binaryWordP12PositiveGapListFinset 12,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP12PositiveGapListFinset_sum_eq_gapVector_sum K N 12]
    _ = (12 : ℂ) *
        ∑ rep ∈ binaryWordP12GapOrbitReps12,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP12GapTraceOrbitSum12 K N]


/-- Normalized p=12, r=12 word stratum in its exact cyclic classes. -/
theorem binaryWordP12WordTraceOrbitAverage12
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 12 12,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP12GapOrbitReps12,
      ((12 : ℂ) / (12 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) * cyclicGapTrace K N rep := by
  apply binaryWordP12_normalize_weighted_orbit_sum K N 12 (by norm_num)
    binaryWordP12GapOrbitReps12
  exact binaryWordP12WordTraceOrbitSum12 K N


end EvgenyTheorem

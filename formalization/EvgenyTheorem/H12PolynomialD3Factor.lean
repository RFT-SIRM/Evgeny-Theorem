import EvgenyTheorem.H12PolynomialTargets

namespace EvgenyTheorem

/-- A monomial term in the level-three H12 trace polynomial. -/
noncomputable def h12D3FactorTerm (a b : ℕ) (k : ℤ) : H12Poly :=
  (k : H12Poly) * h12c ^ a * h12s ^ b

/-- Candidate level-three trace polynomial, transcribed from the exact sparse
coefficient calculation. This declaration alone does not identify it with the
operator trace; that identification is a separate theorem still to be proved. -/
noncomputable def h12D3RawPolynomial : H12Poly :=
    h12D3FactorTerm 0 2 (-12470932128)
  + h12D3FactorTerm 0 3 285009216
  + h12D3FactorTerm 0 4 (-5089544880)
  + h12D3FactorTerm 0 5 (-152326848)
  + h12D3FactorTerm 0 6 (-560827936)
  + h12D3FactorTerm 0 7 (-20895936)
  + h12D3FactorTerm 0 8 (-16744080)
  + h12D3FactorTerm 0 9 (-380352)
  + h12D3FactorTerm 0 10 (-62880)
  + h12D3FactorTerm 1 2 7341160896
  + h12D3FactorTerm 1 3 (-80677152)
  + h12D3FactorTerm 1 4 1409666688
  + h12D3FactorTerm 1 5 1289856
  + h12D3FactorTerm 1 6 67332672
  + h12D3FactorTerm 1 7 40320
  + h12D3FactorTerm 1 8 739392
  + h12D3FactorTerm 2 2 (-6002023920)
  + h12D3FactorTerm 2 3 (-154263936)
  + h12D3FactorTerm 2 4 (-1180398528)
  + h12D3FactorTerm 2 5 (-42014592)
  + h12D3FactorTerm 2 6 (-50563152)
  + h12D3FactorTerm 2 7 (-1141056)
  + h12D3FactorTerm 2 8 (-251520)
  + h12D3FactorTerm 3 2 1484289984
  + h12D3FactorTerm 3 3 2647680
  + h12D3FactorTerm 3 4 136851072
  + h12D3FactorTerm 3 5 95424
  + h12D3FactorTerm 3 6 2218176
  + h12D3FactorTerm 4 2 (-622111776)
  + h12D3FactorTerm 4 3 (-21183936)
  + h12D3FactorTerm 4 4 (-50916720)
  + h12D3FactorTerm 4 5 (-1141056)
  + h12D3FactorTerm 4 6 (-377280)
  + h12D3FactorTerm 5 2 69551424
  + h12D3FactorTerm 5 3 55872
  + h12D3FactorTerm 5 4 2218176
  + h12D3FactorTerm 6 2 (-17098032)
  + h12D3FactorTerm 6 3 (-380352)
  + h12D3FactorTerm 6 4 (-251520)
  + h12D3FactorTerm 7 2 739392
  + h12D3FactorTerm 8 2 (-62880)

/-- Exact quotient in the circle reduction by c²+s²-1. -/
noncomputable def h12D3CircleQuotient : H12Poly :=
    h12D3FactorTerm 0 2 (-5667179776)
  + h12D3FactorTerm 0 3 (-173603136)
  + h12D3FactorTerm 0 4 (-577634896)
  + h12D3FactorTerm 0 5 (-21276288)
  + h12D3FactorTerm 0 6 (-16806960)
  + h12D3FactorTerm 0 7 (-380352)
  + h12D3FactorTerm 0 8 (-62880)
  + h12D3FactorTerm 1 2 1477738752
  + h12D3FactorTerm 1 3 1330176
  + h12D3FactorTerm 1 4 68072064
  + h12D3FactorTerm 1 5 40320
  + h12D3FactorTerm 1 6 739392
  + h12D3FactorTerm 2 2 (-636708464)
  + h12D3FactorTerm 2 3 (-21499008)
  + h12D3FactorTerm 2 4 (-33944832)
  + h12D3FactorTerm 2 5 (-760704)
  + h12D3FactorTerm 2 6 (-188640)
  + h12D3FactorTerm 3 2 70257792
  + h12D3FactorTerm 3 3 55104
  + h12D3FactorTerm 3 4 1478784
  + h12D3FactorTerm 4 2 (-17160528)
  + h12D3FactorTerm 4 3 (-380352)
  + h12D3FactorTerm 4 4 (-188640)
  + h12D3FactorTerm 5 2 739392
  + h12D3FactorTerm 6 2 (-62880)

/-- The candidate coefficients factor to 32*s²*Q₃ modulo the unit-circle
relation. This is a purely algebraic coefficient identity. -/
theorem h12D3Raw_circle_relation :
    h12D3RawPolynomial - 32 * h12s ^ 2 * h12Q3 =
      (h12c ^ 2 + h12s ^ 2 - 1) * h12D3CircleQuotient := by
  simp only [h12D3RawPolynomial, h12D3CircleQuotient,
    h12D3FactorTerm, h12Q3, h12c, h12s]
  ring_nf

end EvgenyTheorem

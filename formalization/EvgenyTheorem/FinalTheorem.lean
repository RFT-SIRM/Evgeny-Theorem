import EvgenyTheorem.FinalTilde

namespace EvgenyTheorem

open Matrix

theorem traceDefect_eq_oNum (m : ℕ) (θ : ℝ) :
    traceDefect m θ = defectO m θ faceAxis (fun _ => 2) (oNum m) := by
  rw [traceDefect_eq_defectO]
  first
    | rfl
    | (congr 1; exact Subsingleton.elim _ _)
    | (unfold oNum; congr 1; exact Subsingleton.elim _ _)
    | (convert rfl)

/-- **Closed form of the trace defect**, given the flipped-corner base case. -/
theorem traceDefect_formula
    (hbase : ∀ θ : ℝ, defectO 1 θ faceAxis (fun _ => 2) (oTil 1) = 0)
    (θ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    traceDefect m θ =
      -16 * ((3 : ℂ) ^ (m - 1) + 1) * ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2 := by
  have h1 : defectO 1 θ faceAxis (fun _ => 2) (oNum 1) =
      -32 * ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2 :=
    (traceDefect_eq_oNum 1 θ).symm.trans (traceDefect_one θ)
  have key := defect_closed_form
    (fun n => defectO n θ faceAxis (fun _ => 2) (oNum n))
    (fun n => defectO n θ faceAxis (fun _ => 2) (oTil n))
    (((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2) h1 (hbase θ)
    (fun n hn => defect_succ_num n hn θ) (fun n hn => defect_succ_til n hn θ) m hm
  rw [traceDefect_eq_oNum]
  exact key.1

end EvgenyTheorem

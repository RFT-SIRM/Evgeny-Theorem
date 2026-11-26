import EvgenyTheorem.FinalClosed12

namespace EvgenyTheorem

/--
The level-five residual constant is exactly reducible to a finite
level-three expression.

The reduction uses:
* transport of the positive-even H12 boundary term from level 3 to level 5;
* invariance of the orientation gap from level 3 to level 5;
* orientation independence of the positive-even boundary term at level 3.

No numerical assumption is used.
-/
theorem defectO12_num_residual_constant_eq_level3
    (θ : ℝ) :
    defectO12_num_residual_constant θ =
      (glueRHS12 3 (sgK 3 θ faceAxis (oNum 4)) -
        glueRHS12 3 (sgK 3 θ (fun _ => 2) (oNum 4))) -
      (defectO12 3 θ faceAxis (fun _ => 2) (oNum 3) -
        defectO12 3 θ faceAxis (fun _ => 2) (oTil 3)) := by
  unfold defectO12_num_residual_constant
  rw [
    ← glueRHS12_sgK_til_eq_level5_faceAxis_from_level3
        θ 3 le_rfl,
    ← glueRHS12_sgK_til_eq_level5_constAxis_from_level3
        θ 3 le_rfl,
    ← defectO12_orientation_difference_eq_level5_from_level3
        3 le_rfl θ,
    ← glueRHS12_num_eq_til_level3
        3 le_rfl θ faceAxis,
    ← glueRHS12_num_eq_til_level3
        3 le_rfl θ (fun _ => 2)
  ]

end EvgenyTheorem

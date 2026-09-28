import EvgenyTheorem.Operator

/-!
# Level-4 structural checks (slow)

Same facts as the named theorems at the end of `SanityChecks.lean`, for
`m = 4` (123 vertices), still by plain kernel-checked `decide`. Kept in a
separate file that is *not* imported by `EvgenyTheorem.lean` because it
takes about three minutes. Build explicitly with
`lake build EvgenyTheorem.SanityChecksLevel4`.
-/

namespace EvgenyTheorem

set_option maxRecDepth 1000000 in
theorem card_degree_two_level4 :
    (Finset.univ.filter (fun v : Vertex 4 => degree 4 v = 2)).card = 3 := by
  decide

set_option maxRecDepth 1000000 in
theorem degrees_are_two_or_four_level4 :
    ∀ v : Vertex 4, degree 4 v = 2 ∨ degree 4 v = 4 := by
  decide

end EvgenyTheorem

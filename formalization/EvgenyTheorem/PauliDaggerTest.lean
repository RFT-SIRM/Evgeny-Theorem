import EvgenyTheorem.Operator

namespace EvgenyTheorem

example : Matrix.conjTranspose pauliX = pauliX := by
  simp [pauliX]

example : Matrix.conjTranspose pauliY = pauliY := by
  simp [pauliY]

example : Matrix.conjTranspose pauliZ = pauliZ := by
  simp [pauliZ]

end EvgenyTheorem

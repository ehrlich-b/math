import PaperA.Spec.Observations

open PaperA PaperA.Spec.Observations

#print axioms transpose_orientation

example : (coordSlot star (0 : Fin 2) 1 Complex.I).transpose 0 1 = -Complex.I := by
  simp [coordSlot, Matrix.transpose_apply]

example : (coordSlot star (0 : Fin 2) 1 Complex.I).transpose 1 0 = Complex.I := by
  simp [coordSlot, Matrix.transpose_apply]

example : (coordSlot star (0 : Fin 2) 1 Complex.I).transpose ≠
    coordSlot star (0 : Fin 2) 1 Complex.I := by
  intro h
  have h' := congrFun (congrFun h 0) 1
  simp [coordSlot, Matrix.transpose_apply] at h'
  have h'' := congrArg Complex.im h'
  norm_num at h''

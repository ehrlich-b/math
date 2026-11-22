import PaperA.Spec.PeirceComplexLinearity

noncomputable section
open PaperA.Spec.Observations

example : peirceAction 0 1 1 (Complex.I * (1 + 2 * Complex.I)) =
    Complex.I * peirceAction 0 1 1 (1 + 2 * Complex.I) :=
  peirceAction_complex_mul 0 1 1 Complex.I (1 + 2 * Complex.I)

example : peirceAction 0 1 1 (Complex.I * (3 - Complex.I)) =
    Complex.I * peirceAction 0 1 1 (3 - Complex.I) :=
  peirceAction_complex_mul 0 1 1 Complex.I (3 - Complex.I)

example : (1 + 2 * Complex.I : ℂ) ≠ 3 - Complex.I := by
  intro h
  have h' := congrArg Complex.re h
  norm_num at h'

example (t : ℝ) (z : ℂ) : peirceAction t 0 1 (Complex.I * z) = 0 := by
  simp [peirceAction]

example (t : ℝ) (z : ℂ) : peirceAction t (-1) 1 (Complex.I * z) = 0 := by
  simp [peirceAction]

example : peirceAction 0 1 1 (Complex.I * 1) ≠
    star Complex.I * peirceAction 0 1 1 1 := by
  simp [peirceAction]
  intro h
  have h' := congrArg Complex.im h
  norm_num at h'

#print axioms peirceAction_complex_mul
#print axioms peirceAction_map_zero
#print axioms peirceAction_sub

import PaperA.Spec.PeirceNorm

noncomputable section
open PaperA.Spec.Observations

-- Direct controls use the original definition rather than the norm theorem.
example (t y : ℝ) (z : ℂ) : ‖peirceAction t 0 y z‖ = 0 := by
  simp [peirceAction]

example (t x : ℝ) (z : ℂ) : ‖peirceAction t x 0 z‖ = 0 := by
  simp [peirceAction]

example (t : ℝ) : ‖peirceAction t 1 1 1‖ = 1 := by
  simp [peirceAction]

example : ‖peirceAction 0 4 9 1‖ = 6 := by
  have hs : Real.sqrt 36 = 6 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num [peirceAction, hs]

-- Doubling the amplitude fails the proposed identity even at unit inputs.
example : ‖(2 : ℂ) * ((Real.sqrt (1*1) : ℂ) *
    Complex.exp (Complex.I * ((0 : ℝ) * Real.log (1/1))) * 1)‖ ≠
    Real.sqrt (1*1) * ‖(1 : ℂ)‖ := by
  norm_num

#print axioms peirceAction_norm
#print axioms peirceAction_norm_sq

import PaperA.Spec.PeirceNormSquare

noncomputable section
open PaperA.Spec.Observations

-- These controls reduce the declared action directly, without the theorem.
example : Complex.normSq (peirceAction 0 4 9 (1 + Complex.I)) = 72 := by
  have hs : Real.sqrt 36 = 6 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num [peirceAction, hs, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

example (t : ℝ) : Complex.normSq (peirceAction t (-2) (-3) (1 + Complex.I)) = 0 := by
  norm_num [peirceAction]

example (t y : ℝ) (z : ℂ) : Complex.normSq (peirceAction t 0 y z) = 0 := by
  simp [peirceAction]

example (t x : ℝ) (z : ℂ) : Complex.normSq (peirceAction t x 0 z) = 0 := by
  simp [peirceAction]

-- The unguarded formula is false even though the product of the inputs is positive.
example : Complex.normSq (peirceAction 0 (-2) (-3) (1 + Complex.I)) ≠
    ((-2 : ℝ) * (-3)) * Complex.normSq (1 + Complex.I) := by
  norm_num [peirceAction, Complex.normSq_apply]

#print axioms peirceAction_normSq

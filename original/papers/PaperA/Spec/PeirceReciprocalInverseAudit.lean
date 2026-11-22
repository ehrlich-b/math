import PaperA.Spec.PeirceReciprocalInverse

noncomputable section
open PaperA.Spec.Observations

-- Unequal positive eigenvalues, with a non-real input and arbitrary time.
example (t : ℝ) : peirceAction t (1/4) (1/9)
    (peirceAction t 4 9 (3 + 2 * Complex.I)) = 3 + 2 * Complex.I :=
  peirceAction_reciprocal_left t 4 9 (by norm_num) (by norm_num) _

example (t : ℝ) : peirceAction t 4 9
    (peirceAction t (1/4) (1/9) (3 + 2 * Complex.I)) = 3 + 2 * Complex.I :=
  peirceAction_reciprocal_right t 4 9 (by norm_num) (by norm_num) _

example : peirceAction 0 (1/4) (1/9)
    (peirceAction 0 4 9 (3 + 2 * Complex.I)) = 3 + 2 * Complex.I := by
  have h4 : Real.sqrt (4 : ℝ) = 2 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have h9 : Real.sqrt (9 : ℝ) = 3 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  simp [peirceAction, h4, h9]
  ring

-- Dropping strict positivity makes inversion fail, even at time zero.
example : peirceAction 0 (1/(0 : ℝ)) (1/(9 : ℝ))
    (peirceAction 0 0 9 (1 : ℂ)) ≠ 1 := by
  simp [peirceAction]

#print axioms peirceAction_reciprocal_left
#print axioms peirceAction_reciprocal_right

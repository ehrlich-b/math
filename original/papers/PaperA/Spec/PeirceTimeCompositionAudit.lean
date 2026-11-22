import PaperA.Spec.PeirceTimeComposition

noncomputable section
open PaperA.Spec.Observations

-- Unequal positive eigenvalues and a non-real coherence coordinate.
example (s t : ℝ) : peirceAction s 4 9 (peirceAction t 4 9 Complex.I) =
    (Real.sqrt (4*9) : ℂ) * peirceAction (s+t) 4 9 Complex.I :=
  peirceAction_time_composition s t 4 9 Complex.I

example (s t y : ℝ) (z : ℂ) : peirceAction s 0 y (peirceAction t 0 y z) = 0 := by
  simp [peirceAction]

example (s t x : ℝ) (z : ℂ) (hx : x ≤ 0) :
    peirceAction s x 2 (peirceAction t x 2 z) = 0 := by
  simp [peirceAction, not_lt_of_ge hx]

-- At zero time the amplitude is 6, so unscaled composition is false.
example : peirceAction 0 4 9 (peirceAction 0 4 9 Complex.I) ≠
    peirceAction 0 4 9 Complex.I := by
  have hs4 : Real.sqrt 4 = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have hs9 : Real.sqrt 9 = 3 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  simp [peirceAction, hs4, hs9]
  norm_num

#print axioms peirceAction_time_composition

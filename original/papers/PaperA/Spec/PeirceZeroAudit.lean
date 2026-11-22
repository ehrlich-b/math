import PaperA.Spec.Observations

open PaperA.Spec.Observations

example (t y : ℝ) (hy : 0 ≤ y) (z : ℂ) : peirceAction t 0 y z = 0 := by
  simp [peirceAction]

example (t x : ℝ) (hx : 0 ≤ x) (z : ℂ) : peirceAction t x 0 z = 0 := by
  simp [peirceAction]

example (t : ℝ) (z : ℂ) : peirceAction t 0 0 z = 0 := by
  simp [peirceAction]

example : peirceAction 0 1 1 1 ≠ 0 := by
  simp [peirceAction]

#print axioms peirceAction_zero

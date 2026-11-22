import Mathlib.Tactic
import PaperA.Spec.PeircePositiveScaling

noncomputable section
open PaperA.Spec.Observations

-- These controls reduce the definition directly, independently of the theorem.
example (t x y : ℝ) (z : ℂ) :
    peirceAction t (0*x) (0*y) z = (0 : ℂ) * peirceAction t x y z := by
  simp [peirceAction]

example (t x y : ℝ) (z : ℂ) :
    peirceAction t (1*x) (1*y) z = (1 : ℂ) * peirceAction t x y z := by
  simp

example : peirceAction 0 (2*1) (2*4) (1 + Complex.I) =
    (2 : ℂ) * peirceAction 0 1 4 (1 + Complex.I) := by
  norm_num [peirceAction]
  ring

example (t r y : ℝ) (hr : 0 ≤ r) (z : ℂ) :
    peirceAction t (r*(-1)) (r*y) z = 0 := by
  have h : ¬ (0 < r*(-1) ∧ 0 < r*y) := by
    intro h
    nlinarith [h.1]
  simp only [peirceAction, if_neg h]

example (t r x : ℝ) (z : ℂ) :
    peirceAction t (r*x) (r*0) z = 0 := by
  simp [peirceAction]

-- Negative scaling is not a valid extension of the theorem.
example : peirceAction 0 ((-1)*1) ((-1)*1) 1 ≠
    ((-1 : ℝ) : ℂ) * peirceAction 0 1 1 1 := by
  norm_num [peirceAction]

#print axioms peirceAction_positive_scaling

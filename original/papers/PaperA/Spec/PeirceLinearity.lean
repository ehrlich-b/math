import PaperA.Spec.Observations

/-! Linearity of the declared coordinate action, independently of the unfinished
bridge from sequential products to that action. -/

noncomputable section
namespace PaperA.Spec.Observations

theorem peirceAction_add (t x y : ℝ) (z w : ℂ) :
    peirceAction t x y (z + w) = peirceAction t x y z + peirceAction t x y w := by
  by_cases h : 0 < x ∧ 0 < y
  · simp [peirceAction, h, mul_add]
  · simp [peirceAction, h]

theorem peirceAction_smul (t x y a : ℝ) (z : ℂ) :
    peirceAction t x y (a • z) = a • peirceAction t x y z := by
  by_cases h : 0 < x ∧ 0 < y
  · simp only [peirceAction, if_pos h, Complex.real_smul]
    ring
  · simp [peirceAction, h]

end PaperA.Spec.Observations

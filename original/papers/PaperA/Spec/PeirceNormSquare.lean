import PaperA.Spec.PeirceNorm

noncomputable section

namespace PaperA.Spec.Observations

/-- The declared action has time-independent squared norm, including its zero branch. -/
theorem peirceAction_normSq (t x y : ℝ) (z : ℂ) :
    Complex.normSq (peirceAction t x y z) =
      (if 0 < x ∧ 0 < y then x*y else 0) * Complex.normSq z := by
  by_cases h : 0 < x ∧ 0 < y
  · rw [if_pos h, ← Complex.sq_norm, ← Complex.sq_norm]
    exact peirceAction_norm_sq t x y h.1.le h.2.le z
  · simp [peirceAction, h]

end PaperA.Spec.Observations

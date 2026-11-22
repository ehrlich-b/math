import PaperA.Spec.Observations

/-! Conjugation reverses the twist of the declared coordinate action. This does
not prove the unfinished `peirce_action_formula` bridge to the actual product. -/
noncomputable section
namespace PaperA.Spec.Observations

theorem peirceAction_conj (t x y : ℝ) (z : ℂ) :
    star (peirceAction t x y z) = peirceAction (-t) x y (star z) := by
  by_cases h : 0 < x ∧ 0 < y
  · simp [peirceAction, h, map_mul, ← Complex.exp_conj, Complex.conj_I,
      neg_mul]
  · simp [peirceAction, h]

theorem peirceAction_conj_zero (x y : ℝ) (z : ℂ) :
    star (peirceAction 0 x y z) = peirceAction 0 x y (star z) := by
  simpa using peirceAction_conj 0 x y z

end PaperA.Spec.Observations

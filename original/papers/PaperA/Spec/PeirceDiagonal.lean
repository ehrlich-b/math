import PaperA.Spec.Observations

noncomputable section

namespace PaperA.Spec.Observations

/-- Equal nonnegative eigenvalues eliminate the logarithmic twist, including zero. -/
theorem peirceAction_diagonal (t x : ℝ) (hx : 0 ≤ x) (z : ℂ) :
    peirceAction t x x z = (x : ℂ) * z := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [peirceAction]
  · have hx0 : x ≠ 0 := ne_of_gt hx
    simp [peirceAction, hx, hx0, Real.sqrt_mul_self hx.le]

/-- At zero twist the action is the geometric mean on positive eigenvalues. -/
theorem peirceAction_zero_twist (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    peirceAction 0 x y z = (Real.sqrt (x * y) : ℂ) * z := by
  simp [peirceAction, hx, hy]

end PaperA.Spec.Observations

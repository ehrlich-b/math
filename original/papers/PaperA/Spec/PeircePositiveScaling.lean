import PaperA.Spec.Observations

/-! Joint positive scaling of the declared coordinate action. This does not
prove the bridge to the actual sequential product. -/

noncomputable section
namespace PaperA.Spec.Observations

/-- Scaling both eigenvalues by a nonnegative real scales the action. -/
theorem peirceAction_positive_scaling (r t x y : ℝ) (hr : 0 ≤ r) (z : ℂ) :
    peirceAction t (r*x) (r*y) z = (r : ℂ) * peirceAction t x y z := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [peirceAction]
  · by_cases h : 0 < x ∧ 0 < y
    · have hs : 0 < r*x ∧ 0 < r*y := ⟨mul_pos hr h.1, mul_pos hr h.2⟩
      have hratio : (r*x)/(r*y) = x/y := by field_simp
      have hsqrt : Real.sqrt ((r*x)*(r*y)) = r * Real.sqrt (x*y) := by
        rw [show (r*x)*(r*y) = r^2*(x*y) by ring, Real.sqrt_mul (sq_nonneg r),
          Real.sqrt_sq (le_of_lt hr)]
      simp only [peirceAction, if_pos h, if_pos hs, hratio, hsqrt, Complex.ofReal_mul]
      ring
    · have hs : ¬ (0 < r*x ∧ 0 < r*y) := by
        intro hs
        apply h
        constructor <;> nlinarith
      simp [peirceAction, h, hs]

end PaperA.Spec.Observations

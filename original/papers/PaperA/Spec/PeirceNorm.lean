import PaperA.Spec.Observations

noncomputable section

namespace PaperA.Spec.Observations

/-- The twist rotates the coherence coordinate without changing its norm. -/
theorem peirceAction_norm (t x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℂ) :
    ‖peirceAction t x y z‖ = Real.sqrt (x*y) * ‖z‖ := by
  by_cases h : 0 < x ∧ 0 < y
  · rw [peirceAction, if_pos h, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), ← Complex.ofReal_mul,
      Complex.norm_exp_I_mul_ofReal, mul_one]
  · have hxy : x*y = 0 := by
      have : x = 0 ∨ y = 0 := by
        rcases lt_or_eq_of_le hx with hx' | hx'
        · rcases lt_or_eq_of_le hy with hy' | hy'
          · exact False.elim (h ⟨hx', hy'⟩)
          · exact Or.inr hy'.symm
        · exact Or.inl hx'.symm
      rcases this with rfl | rfl <;> simp
    simp [peirceAction, h, hxy]

/-- The corresponding squared norm, including singular eigenvalues. -/
theorem peirceAction_norm_sq (t x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℂ) :
    ‖peirceAction t x y z‖ ^ 2 = x*y * ‖z‖ ^ 2 := by
  rw [peirceAction_norm t x y hx hy, mul_pow, Real.sq_sqrt (mul_nonneg hx hy)]

end PaperA.Spec.Observations

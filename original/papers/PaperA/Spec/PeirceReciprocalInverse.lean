import PaperA.Spec.Observations

noncomputable section

namespace PaperA.Spec.Observations

/-- Reciprocal positive eigenvalues undo the Peirce action at the same time. -/
theorem peirceAction_reciprocal_left (t x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (z : ℂ) : peirceAction t (1/x) (1/y) (peirceAction t x y z) = z := by
  have ha : Real.sqrt ((1/x)*(1/y)) = (Real.sqrt (x*y))⁻¹ := by
    rw [show (1/x)*(1/y) = (x*y)⁻¹ by simp [one_div, mul_inv_rev, mul_comm], Real.sqrt_inv]
  have hl : Real.log ((1/x)/(1/y)) = -Real.log (x/y) := by
    rw [show (1/x)/(1/y) = (x/y)⁻¹ by simp [div_eq_mul_inv, mul_comm], Real.log_inv]
  have hs : (Real.sqrt (x*y) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (mul_pos hx hy)))
  have h : 0 < x ∧ 0 < y := ⟨hx, hy⟩
  have hi : 0 < 1/x ∧ 0 < 1/y := ⟨one_div_pos.mpr hx, one_div_pos.mpr hy⟩
  simp only [peirceAction, if_pos h, if_pos hi, ha, hl]
  push_cast
  have he : Complex.exp (Complex.I * (t * -(Real.log (x / y)))) =
      (Complex.exp (Complex.I * (t * Real.log (x / y))))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    ring
  rw [he]
  have hn := Complex.exp_ne_zero (Complex.I * (t * Real.log (x / y)))
  field_simp

/-- The reverse composition is also the identity. -/
theorem peirceAction_reciprocal_right (t x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (z : ℂ) : peirceAction t x y (peirceAction t (1/x) (1/y) z) = z := by
  simpa using peirceAction_reciprocal_left t (1/x) (1/y) (one_div_pos.mpr hx)
    (one_div_pos.mpr hy) z

end PaperA.Spec.Observations

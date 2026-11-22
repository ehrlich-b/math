import PaperA.Spec.PeirceInjective

noncomputable section

namespace PaperA.Spec.Observations

/-- Positive eigenvalues make the declared complex scalar action surjective. -/
theorem peirceAction_surjective (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Function.Surjective (peirceAction t x y) := by
  have hc : (Real.sqrt (x*y) : ℂ) *
      Complex.exp (Complex.I * (t*Real.log (x/y))) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (mul_pos hx hy)))
    · exact Complex.exp_ne_zero _
  intro w
  refine ⟨((Real.sqrt (x*y) : ℂ) *
      Complex.exp (Complex.I * (t*Real.log (x/y))))⁻¹ * w, ?_⟩
  have hxy : 0 < x ∧ 0 < y := ⟨hx, hy⟩
  simp only [peirceAction, if_pos hxy]
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- The positive scalar action is a bijection on complex coherences. -/
theorem peirceAction_bijective (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Function.Bijective (peirceAction t x y) :=
  ⟨peirceAction_injective t x y hx hy, peirceAction_surjective t x y hx hy⟩

/-- The zero-eigenvalue branch cannot reach a nonzero complex target. -/
theorem peirceAction_zero_left_not_surjective (t y : ℝ) :
    ¬ Function.Surjective (peirceAction t 0 y) := by
  intro h
  obtain ⟨z, hz⟩ := h 1
  have : (0 : ℂ) = 1 := by simpa [peirceAction] using hz
  exact zero_ne_one this

/- This concerns the declared scalar action. The sequential-product bridge
`peirce_action_formula` remains unproved. -/
end PaperA.Spec.Observations

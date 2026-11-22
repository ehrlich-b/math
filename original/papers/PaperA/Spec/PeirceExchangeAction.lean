import PaperA.Spec.Observations

noncomputable section
namespace PaperA.Spec.Observations

/-- Exchanging the eigenvalues reverses the twist, for all real inputs. -/
theorem peirceAction_exchange (t x y : ℝ) (z : ℂ) :
    peirceAction t y x z = peirceAction (-t) x y z := by
  by_cases h : 0 < x ∧ 0 < y
  · have hs : 0 < y ∧ 0 < x := ⟨h.2, h.1⟩
    have hl : Real.log (y / x) = -Real.log (x / y) := by
      rw [show y / x = (x / y)⁻¹ by field_simp, Real.log_inv]
    simp only [peirceAction, if_pos h, if_pos hs, mul_comm y x, hl, Complex.ofReal_neg, neg_mul, mul_neg]
  · have hs : ¬ (0 < y ∧ 0 < x) := by simpa [and_comm] using h
    simp [peirceAction, h, hs]

/-- At zero twist, exchanging the eigenvalues leaves the action unchanged. -/
theorem peirceAction_exchange_zero (x y : ℝ) (z : ℂ) :
    peirceAction 0 y x z = peirceAction 0 x y z := by
  simpa using peirceAction_exchange 0 x y z

end PaperA.Spec.Observations

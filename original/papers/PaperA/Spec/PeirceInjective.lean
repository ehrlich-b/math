import PaperA.Spec.Observations
import PaperA.Spec.PeirceNorm

noncomputable section

namespace PaperA.Spec.Observations

/-- Positive eigenvalues preserve every distinction between complex coherences. -/
theorem peirceAction_injective (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Function.Injective (peirceAction t x y) := by
  have hc : (Real.sqrt (x*y) : ℂ) *
      Complex.exp (Complex.I * (t*Real.log (x/y))) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (mul_pos hx hy)))
    · exact Complex.exp_ne_zero _
  intro z w h
  have hxy : 0 < x ∧ 0 < y := ⟨hx, hy⟩
  simp only [peirceAction, if_pos hxy] at h
  exact mul_left_cancel₀ hc h

/-- A positive block action annihilates exactly the zero coherence. -/
theorem peirceAction_eq_zero_iff (t x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (z : ℂ) : peirceAction t x y z = 0 ↔ z = 0 := by
  have hzero : peirceAction t x y 0 = 0 := by simp [peirceAction]
  constructor
  · intro h
    exact peirceAction_injective t x y hx hy (h.trans hzero.symm)
  · rintro rfl
    exact hzero

/-- A zero eigenvalue makes the action noninjective, independently of the
positive case. -/
theorem peirceAction_zero_left_not_injective (t y : ℝ) :
    ¬ Function.Injective (peirceAction t 0 y) := by
  intro h
  have h01 : (0 : ℂ) = 1 := h (by simp [peirceAction])
  exact zero_ne_one h01

/- This is a scalar-coordinate result; the bridge to the actual product,
`peirce_action_formula`, remains unproved. -/
end PaperA.Spec.Observations

import PaperA.Spec.Observations

noncomputable section

namespace PaperA.Spec.Observations

/-- Composition carries one additional copy of the Peirce amplitude. -/
theorem peirceAction_time_composition (s t x y : ℝ) (z : ℂ) :
    peirceAction s x y (peirceAction t x y z) =
      (Real.sqrt (x*y) : ℂ) * peirceAction (s+t) x y z := by
  by_cases h : 0 < x ∧ 0 < y
  · simp only [peirceAction, if_pos h]
    have hexp : Complex.exp (Complex.I * ((s+t)*Real.log (x/y))) =
        Complex.exp (Complex.I * (s*Real.log (x/y))) *
          Complex.exp (Complex.I * (t*Real.log (x/y))) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    push_cast
    rw [hexp]
    ring
  · simp [peirceAction, h]

end PaperA.Spec.Observations

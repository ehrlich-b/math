import PaperA.Spec.PeirceLinearity

/-! Complex linearity of the declared coordinate action. This does not prove
its bridge to sequential products. -/

noncomputable section
namespace PaperA.Spec.Observations

theorem peirceAction_complex_mul (t x y : ℝ) (c z : ℂ) :
    peirceAction t x y (c * z) = c * peirceAction t x y z := by
  by_cases h : 0 < x ∧ 0 < y
  · simp only [peirceAction, if_pos h]
    ring
  · simp [peirceAction, h]

theorem peirceAction_map_zero (t x y : ℝ) : peirceAction t x y 0 = 0 := by
  simpa using peirceAction_complex_mul t x y 0 0

theorem peirceAction_sub (t x y : ℝ) (z w : ℂ) :
    peirceAction t x y (z - w) = peirceAction t x y z - peirceAction t x y w := by
  rw [sub_eq_add_neg, peirceAction_add, sub_eq_add_neg]
  simpa using congrArg (fun u => peirceAction t x y z + u)
    (peirceAction_complex_mul t x y (-1) w)

end PaperA.Spec.Observations

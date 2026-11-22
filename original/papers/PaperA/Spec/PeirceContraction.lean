import PaperA.Spec.Observations
import PaperA.Spec.PeirceNorm

noncomputable section
namespace PaperA.Spec.Observations

/-- The coordinate action respects differences, including the singular branch. -/
theorem peirceAction_sub (t x y : ℝ) (z w : ℂ) :
    peirceAction t x y (z - w) = peirceAction t x y z - peirceAction t x y w := by
  by_cases h : 0 < x ∧ 0 < y
  · simp [peirceAction, h, mul_sub]
  · simp [peirceAction, h]

/-- Effect eigenvalues give a norm contraction for every twist. -/
theorem peirceAction_norm_le (t x y : ℝ) (hx : x ∈ Set.Icc 0 1)
    (hy : y ∈ Set.Icc 0 1) (z : ℂ) : ‖peirceAction t x y z‖ ≤ ‖z‖ := by
  rw [peirceAction_norm t x y hx.1 hy.1]
  have hxy : x * y ≤ 1 := by nlinarith [hy.2, mul_nonneg (sub_nonneg.mpr hx.2) hy.1]
  have hs : Real.sqrt (x * y) ≤ 1 := by
    exact (Real.sqrt_le_one).2 hxy
  nlinarith [norm_nonneg z, Real.sqrt_nonneg (x * y)]

/-- Distances between arbitrary coherence coordinates do not increase. -/
theorem peirceAction_dist_le (t x y : ℝ) (hx : x ∈ Set.Icc 0 1)
    (hy : y ∈ Set.Icc 0 1) (z w : ℂ) :
    dist (peirceAction t x y z) (peirceAction t x y w) ≤ dist z w := by
  rw [dist_eq_norm, ← peirceAction_sub, dist_eq_norm]
  exact peirceAction_norm_le t x y hx hy (z - w)

/-- Either zero eigenvalue annihilates every coordinate. -/
theorem peirceAction_zero_eigenvalue (t x y : ℝ) (h : x = 0 ∨ y = 0) (z : ℂ) :
    peirceAction t x y z = 0 := by
  rcases h with rfl | rfl <;> simp [peirceAction]

end PaperA.Spec.Observations

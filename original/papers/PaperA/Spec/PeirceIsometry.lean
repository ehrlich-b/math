import PaperA.Spec.PeirceComplexLinearity
import PaperA.Spec.PeirceNorm

noncomputable section
namespace PaperA.Spec.Observations

/-- A unit product of positive eigenvalues preserves coherence distances. -/
theorem peirceAction_dist (t x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 1) (z w : ℂ) :
    dist (peirceAction t x y z) (peirceAction t x y w) = dist z w := by
  rw [dist_eq_norm, ← peirceAction_sub, peirceAction_norm t x y hx.le hy.le,
    hxy, Real.sqrt_one, one_mul, ← dist_eq_norm]

/-- The scalar action is an isometry when the positive eigenvalues multiply to one. -/
theorem peirceAction_isometry (t x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 1) : Isometry (peirceAction t x y) := by
  exact isometry_iff_dist_eq.mpr (peirceAction_dist t x y hx hy hxy)

end PaperA.Spec.Observations

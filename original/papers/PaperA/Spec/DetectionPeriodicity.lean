import PaperA.Claims

namespace PaperA.Spec

/-- The operational detection probability is periodic in time for nonzero strength. -/
theorem detection_periodic (t r φ : ℝ) (hr : r ≠ 0) :
    detection (t + 2 * Real.pi / r) r φ = detection t r φ := by
  unfold detection
  have h : φ - (t + 2 * Real.pi / r) * r = (φ - t * r) - 2 * Real.pi := by
    field_simp
    <;> ring
  rw [h, Real.cos_sub_two_pi]

example (t φ : ℝ) : detection (t + 2 * Real.pi / 2) 2 φ = detection t 2 φ := by
  exact detection_periodic t 2 φ (by norm_num)

example (t φ : ℝ) : detection (t + 2 * Real.pi / (-2)) (-2) φ = detection t (-2) φ := by
  exact detection_periodic t (-2) φ (by norm_num)

#print axioms detection_periodic

end PaperA.Spec

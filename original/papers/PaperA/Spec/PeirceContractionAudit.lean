import PaperA.Spec.PeirceContraction

noncomputable section
open PaperA.Spec.Observations

-- All distinct complex inputs expand by a factor of six outside the effect domain.
theorem outside_effect_expands (t : ℝ) (z w : ℂ) (h : z ≠ w) :
    dist z w < dist (peirceAction t 4 9 z) (peirceAction t 4 9 w) := by
  simp only [dist_eq_norm]
  rw [← peirceAction_sub, peirceAction_norm t 4 9 (by norm_num) (by norm_num)]
  have hs : Real.sqrt (4 * 9) = 6 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  rw [hs]
  have hp : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  linarith

example (t : ℝ) (z w : ℂ) :
    dist (peirceAction t 1 1 z) (peirceAction t 1 1 w) = dist z w := by
  rw [dist_eq_norm, ← peirceAction_sub,
    peirceAction_norm t 1 1 (by norm_num) (by norm_num), dist_eq_norm]
  simp

example (t : ℝ) (z w : ℂ) :
    dist (peirceAction t 0 1 z) (peirceAction t 0 1 w) = 0 := by
  simp [peirceAction]

#print axioms peirceAction_sub
#print axioms peirceAction_norm_le
#print axioms peirceAction_dist_le
#print axioms peirceAction_zero_eigenvalue
#print axioms outside_effect_expands

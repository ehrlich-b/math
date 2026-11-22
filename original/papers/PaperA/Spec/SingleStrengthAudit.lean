import PaperA.Spec.Observations

open PaperA PaperA.Spec.Observations

#print axioms detection_single_strength_iff

example (s r : ℝ) (hr : 0 < r) :
    detection (s + 2 * Real.pi / r) r 0 = detection s r 0 ∧
    detection (s + 2 * Real.pi / r) r (Real.pi / 2) = detection s r (Real.pi / 2) := by
  apply (detection_single_strength_iff _ _ _ hr).2
  refine ⟨1, ?_⟩
  ring

example (s r : ℝ) (hr : 0 < r) :
    detection (s - 2 * Real.pi / r) r 0 = detection s r 0 ∧
    detection (s - 2 * Real.pi / r) r (Real.pi / 2) = detection s r (Real.pi / 2) := by
  apply (detection_single_strength_iff _ _ _ hr).2
  refine ⟨-1, ?_⟩
  push_cast
  ring

theorem half_period_counterexample : detection Real.pi 1 0 ≠ detection 0 1 0 := by
  have hp := (detection_quadratures Real.pi 1 (by norm_num)).2.2
  have hpi := (detection_quadratures Real.pi 1 (by norm_num)).1
  have hzero := (detection_quadratures 0 1 (by norm_num)).1
  simp only [mul_one, zero_mul, Real.cos_pi, Real.cos_zero] at hpi hzero
  rw [hpi, hzero]
  nlinarith

-- A cosine-only observation cannot replace the pair of quadratures.
theorem cosine_only_counterexample : detection (Real.pi / 2) 1 0 = detection (-Real.pi / 2) 1 0 ∧
    detection (Real.pi / 2) 1 (Real.pi / 2) ≠
      detection (-Real.pi / 2) 1 (Real.pi / 2) := by
  have ht := detection_quadratures (Real.pi / 2) 1 (by norm_num)
  have hs := detection_quadratures (-Real.pi / 2) 1 (by norm_num)
  constructor
  · rw [ht.1, hs.1]
    simp [neg_div]
  · rw [ht.2.1, hs.2.1]
    simp only [mul_one, neg_div, Real.sin_neg, Real.sin_pi_div_two]
    nlinarith [ht.2.2]

-- These negate proposed semantic weakenings, rather than inspecting their text.
example : ¬ (∀ t s : ℝ,
    (detection t 1 0 = detection s 1 0 ∧
      detection t 1 (Real.pi / 2) = detection s 1 (Real.pi / 2)) ↔
      ∃ k : ℤ, t - s = (k : ℝ) * Real.pi) := by
  intro h
  have he := (h Real.pi 0).2 ⟨1, by ring⟩
  exact half_period_counterexample he.1

example : ¬ (∀ t s : ℝ, detection t 1 0 = detection s 1 0 ↔
    ∃ k : ℤ, t - s = (k : ℝ) * (2 * Real.pi / 1)) := by
  intro h
  have shift := (h (Real.pi / 2) (-Real.pi / 2)).1 cosine_only_counterexample.1
  have both := (detection_single_strength_iff _ _ 1 (by norm_num)).2 shift
  exact cosine_only_counterexample.2 both.2

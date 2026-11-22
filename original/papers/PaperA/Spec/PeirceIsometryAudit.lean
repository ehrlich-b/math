import PaperA.Spec.PeirceIsometry

noncomputable section
open PaperA.Spec.Observations

example (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x * y = 1)
    (z w : ℂ) : dist (peirceAction t x y z) (peirceAction t x y w) = dist z w :=
  peirceAction_dist t x y hx hy hxy z w

example (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x * y = 1) :
    Isometry (peirceAction t x y) := peirceAction_isometry t x y hx hy hxy

example (t : ℝ) : Isometry (peirceAction t 1 1) :=
  peirceAction_isometry t 1 1 (by norm_num) (by norm_num) (by norm_num)

-- The norm formula distinguishes the image of 1 from that of 0 at scale 2.
example (t : ℝ) : ¬ Isometry (peirceAction t 2 2) := by
  intro h
  have hd := (isometry_iff_dist_eq.mp h) (1 : ℂ) 0
  have hn := peirceAction_norm t 2 2 (by norm_num) (by norm_num) (1 : ℂ)
  have hs : Real.sqrt (2 * 2 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [hs] at hn
  simp [dist_eq_norm, peirceAction_map_zero] at hd
  norm_num at hn hd
  linarith

-- A zero eigenvalue collapses a nonzero coherence.
example (t : ℝ) : ¬ Isometry (peirceAction t 0 1) := by
  intro h
  have hd := (isometry_iff_dist_eq.mp h) (1 : ℂ) 0
  have hn := peirceAction_norm t 0 1 (by norm_num) (by norm_num) (1 : ℂ)
  simp [dist_eq_norm, peirceAction_map_zero] at hd
  norm_num at hn
  simp [hn] at hd

#print axioms peirceAction_dist
#print axioms peirceAction_isometry

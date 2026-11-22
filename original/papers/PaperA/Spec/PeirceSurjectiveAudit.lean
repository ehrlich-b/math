import PaperA.Spec.PeirceSurjective

open PaperA.Spec.Observations

#print axioms peirceAction_surjective
#print axioms peirceAction_bijective
#print axioms peirceAction_zero_left_not_surjective

-- Unequal eigenvalues, arbitrary time, and a non-real target.
example (t : ℝ) : ∃ z : ℂ, peirceAction t 1 2 z = Complex.I :=
  peirceAction_surjective t 1 2 (by norm_num) (by norm_num) Complex.I

example (t : ℝ) : Function.Bijective (peirceAction t 1 2) :=
  peirceAction_bijective t 1 2 (by norm_num) (by norm_num)

example (t : ℝ) : ¬ Function.Surjective (peirceAction t 0 1) :=
  peirceAction_zero_left_not_surjective t 1

/--
error: unsolved goals
case hx
t : ℝ
⊢ False
-/
#guard_msgs in
example (t : ℝ) : Function.Surjective (peirceAction t 0 1) := by
  apply peirceAction_surjective t 0 1
  · norm_num
  · norm_num

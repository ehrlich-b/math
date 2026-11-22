import PaperA.Spec.PeirceInjective

open PaperA.Spec.Observations

#print axioms peirceAction_injective
#print axioms peirceAction_eq_zero_iff
#print axioms peirceAction_zero_left_not_injective

-- The theorem covers unequal positive eigenvalues and arbitrary complex inputs.
example (t : ℝ) (z w : ℂ) :
    peirceAction t 1 2 z = peirceAction t 1 2 w → z = w :=
  fun h => peirceAction_injective t 1 2 (by norm_num) (by norm_num) h

-- Weakening positivity to nonnegativity is false already at x = 0.
example (t : ℝ) : ¬ Function.Injective (peirceAction t 0 1) :=
  peirceAction_zero_left_not_injective t 1

/--
error: unsolved goals
case hx
t : ℝ
⊢ False
-/
#guard_msgs in
example (t : ℝ) : Function.Injective (peirceAction t 0 1) := by
  apply peirceAction_injective t 0 1
  · norm_num
  · norm_num

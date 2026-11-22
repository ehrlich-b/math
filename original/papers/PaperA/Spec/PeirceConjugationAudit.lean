import PaperA.Spec.PeirceConjugation

noncomputable section
open PaperA.Spec.Observations

-- These controls unfold the action independently of the new theorem.
example : peirceAction 0 4 1 1 = 2 := by
  have h : Real.sqrt 4 = 2 := by
    convert Real.sqrt_mul_self (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> norm_num
  norm_num [peirceAction, h]

example (t : ℝ) : peirceAction t 1 1 1 = 1 := by
  simp [peirceAction]

example (t : ℝ) (z : ℂ) : peirceAction t 0 1 z = 0 := by
  simp [peirceAction]

example (t : ℝ) (z : ℂ) : peirceAction t 1 (-1) z = 0 := by
  norm_num [peirceAction]

example : star (peirceAction 1 (Real.exp (Real.pi / 2)) 1 1) ≠
    peirceAction 1 (Real.exp (Real.pi / 2)) 1 (star (1 : ℂ)) := by
  have hp : 0 < Real.exp (Real.pi / 2) := Real.exp_pos _
  have hs : (Real.sqrt (Real.exp (Real.pi / 2)) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hp))
  have he : Complex.exp (Complex.I * (↑Real.pi / 2)) = Complex.I := by
    rw [mul_comm, Complex.exp_pi_div_two_mul_I]
  simp only [peirceAction, hp, zero_lt_one, and_self, if_true, mul_one,
    div_one, Real.log_exp, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_ofNat, one_mul, he, star_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_I, map_one]
  intro h
  rw [mul_comm (-Complex.I)] at h
  have h' := (mul_left_cancel₀ hs) h
  have hi := congrArg Complex.im h'
  norm_num at hi

#print axioms peirceAction_conj
#print axioms peirceAction_conj_zero

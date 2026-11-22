import PaperA.Spec.PeirceLinearEquiv
import PaperA.Spec.PeirceSurjective
import PaperA.Spec.PeirceDiagonal

noncomputable section

open PaperA.Spec.Observations

-- Omitted hypotheses cannot construct an equivalence for arbitrary eigenvalues.
example (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) : ℂ ≃ₗ[ℂ] ℂ := by
  fail_if_success exact peirceLinearEquiv t x y
  exact peirceLinearEquiv t x y hx hy

-- Exact type and definitional forward and inverse functions.
example : (t x y : ℝ) → 0 < x → 0 < y → ℂ ≃ₗ[ℂ] ℂ := peirceLinearEquiv
example (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ⇑(peirceLinearEquiv t x y hx hy) = peirceAction t x y := rfl
example (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ⇑(peirceLinearEquiv t x y hx hy).symm = peirceAction t (1/x) (1/y) := rfl
example (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    peirceLinearEquiv t x y hx hy z = peirceAction t x y z :=
  peirceLinearEquiv_apply t x y hx hy z
example (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    (peirceLinearEquiv t x y hx hy).symm z = peirceAction t (1/x) (1/y) z :=
  peirceLinearEquiv_symm_apply t x y hx hy z
example (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    (peirceLinearEquiv t x y hx hy).symm (peirceLinearEquiv t x y hx hy z) = z :=
  (peirceLinearEquiv t x y hx hy).symm_apply_apply z
example (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    peirceLinearEquiv t x y hx hy ((peirceLinearEquiv t x y hx hy).symm z) = z :=
  (peirceLinearEquiv t x y hx hy).apply_symm_apply z
example (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) (z w : ℂ) :
    peirceLinearEquiv t x y hx hy (z + w) =
      peirceLinearEquiv t x y hx hy z + peirceLinearEquiv t x y hx hy w :=
  (peirceLinearEquiv t x y hx hy).map_add z w
example (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) (c z : ℂ) :
    peirceLinearEquiv t x y hx hy (c • z) = c • peirceLinearEquiv t x y hx hy z :=
  (peirceLinearEquiv t x y hx hy).map_smul c z
example (t : ℝ) (z : ℂ) : peirceLinearEquiv t 1 1 (by norm_num) (by norm_num) z = z := by
  rw [peirceLinearEquiv_apply, peirceAction_diagonal t 1 (by norm_num)]
  simp
example (t : ℝ) : ¬ Function.Surjective (peirceAction t 0 1) :=
  peirceAction_zero_left_not_surjective t 1
example (t : ℝ) : ¬ ∃ e : ℂ ≃ₗ[ℂ] ℂ, ⇑e = peirceAction t 0 1 := by
  rintro ⟨e, he⟩
  apply peirceAction_zero_left_not_surjective t 1
  rw [← he]
  exact e.surjective

/--
error: unsolved goals
case hx
t : ℝ
⊢ False
-/
#guard_msgs in
example (t : ℝ) : ℂ ≃ₗ[ℂ] ℂ := by
  apply peirceLinearEquiv t 0 1
  · norm_num
  · norm_num

#print axioms peirceLinearEquiv
#print axioms peirceLinearEquiv_apply
#print axioms peirceLinearEquiv_symm_apply
#print axioms peirceAction_reciprocal_left
#print axioms peirceAction_reciprocal_right

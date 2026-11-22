import PaperA.Spec.PeirceComplexLinearity
import PaperA.Spec.PeirceReciprocalInverse

/-! Packaging the declared scalar action; this does not establish the bridge to
sequential products. -/

noncomputable section
namespace PaperA.Spec.Observations

/-- The declared Peirce action is a complex linear equivalence for positive eigenvalues. -/
def peirceLinearEquiv (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) : ℂ ≃ₗ[ℂ] ℂ where
  toFun := peirceAction t x y
  invFun := peirceAction t (1/x) (1/y)
  left_inv := peirceAction_reciprocal_left t x y hx hy
  right_inv := peirceAction_reciprocal_right t x y hx hy
  map_add' := peirceAction_add t x y
  map_smul' c z := peirceAction_complex_mul t x y c z

@[simp] theorem peirceLinearEquiv_apply (t x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (z : ℂ) : peirceLinearEquiv t x y hx hy z = peirceAction t x y z := rfl

@[simp] theorem peirceLinearEquiv_symm_apply (t x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (z : ℂ) : (peirceLinearEquiv t x y hx hy).symm z =
      peirceAction t (1/x) (1/y) z := rfl

end PaperA.Spec.Observations

import PaperA.Definitions
import Mathlib.Tactic.Module

noncomputable section
open EuclideanJordan

namespace PaperA
namespace MatrixDynamics

variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] {n : ℕ}

/-- The normalized commutator of two Hermitian matrices is Hermitian. -/
private theorem commutator_mem (M : ComplexModel J n) (a b : J) :
    ∃ x, M.map x = (Complex.I/2) • (M.map a*M.map b-M.map b*M.map a) := by
  have hs (x : J) : (M.map x).conjTranspose = M.map x := by
    ext i j
    exact (M.range (M.map x)).mp ⟨x, rfl⟩ i j
  apply (M.range _).mpr
  have hstar : star (Complex.I/2) = -(Complex.I/2) := by simp [neg_div]
  have h : ((Complex.I/2) • (M.map a*M.map b-M.map b*M.map a)).conjTranspose =
      (Complex.I/2) • (M.map a*M.map b-M.map b*M.map a) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hs a, hs b, hstar]
    module
  exact fun i j => congrFun (congrFun h i) j

/-- Transfer the real-bilinear normalized commutator through a matrix model. -/
theorem exists_correspondence (M : ComplexModel J n) :
    ∃ ψ : DynamicalCorrespondence J, ∀ a b,
      M.map (ψ.psi a b) = (Complex.I/2) • (M.map a*M.map b-M.map b*M.map a) := by
  classical
  let f (a b : J) : J := Classical.choose (commutator_mem M a b)
  have hf (a b : J) : M.map (f a b) =
      (Complex.I/2) • (M.map a*M.map b-M.map b*M.map a) :=
    Classical.choose_spec (commutator_mem M a b)
  let ψ : J →ₗ[ℝ] J →ₗ[ℝ] J := LinearMap.mk₂ ℝ f
    (by
      intro a b x
      apply M.injective
      simp only [hf, map_add, add_mul, mul_add, smul_sub, smul_add]
      abel)
    (by
      intro r a x
      apply M.injective
      simp only [hf, map_smul, smul_mul_assoc, mul_smul_comm, ← smul_sub]
      exact smul_comm _ _ _)
    (by
      intro a x y
      apply M.injective
      simp only [hf, map_add, add_mul, mul_add, smul_sub, smul_add]
      abel)
    (by
      intro r a x
      apply M.injective
      simp only [hf, map_smul, smul_mul_assoc, mul_smul_comm, ← smul_sub]
      exact smul_comm _ _ _)
  have hψ (a b : J) : M.map (ψ a b) =
      (Complex.I/2) • (M.map a*M.map b-M.map b*M.map a) := hf a b
  have hp (a b : J) : M.map (a*b) =
      (1/2 : ℂ) • (M.map a*M.map b+M.map b*M.map a) := by
    rw [M.product]
    change (1/2 : ℝ) • (M.map a*M.map b+M.map b*M.map a) = _
    rw [← IsScalarTower.algebraMap_smul ℂ (1/2 : ℝ)]
    norm_num
  refine ⟨⟨ψ, ?_, ?_, ?_⟩, hψ⟩
  · intro a x y
    apply M.injective
    simp only [hψ, map_add, hp]
    simp only [smul_add, smul_sub, mul_add, add_mul, mul_sub, sub_mul,
      smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    module
  · intro a
    apply M.injective
    simp [hψ]
  · intro a b x
    -- The two Jordan factors give 1/4, while the commutators give I²/4 = -1/4.
    apply M.injective
    simp only [map_sub, map_neg, hψ, hp]
    simp only [smul_add, smul_sub, mul_add, add_mul, mul_sub, sub_mul,
      smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

end MatrixDynamics
end PaperA

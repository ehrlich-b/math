import PaperA.TransportSequentialProduct

noncomputable section
open EuclideanJordan

namespace PaperA

variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J]

/-- The generic pullback construction supplies the effect-guarded transport witness. -/
theorem exists_jordan_transport (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g)
    (P : SequentialProduct J) :
    ∃ R : SequentialProduct J, ∀ a b, IsEffect a → IsEffect b →
      R.sp a b = g.symm (P.sp (g a) (g b)) := by
  exact ⟨TransportSequentialProduct.transport g hg P, fun _ _ _ _ => rfl⟩

end PaperA

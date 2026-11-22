import PaperA.Octonion
import Lean.Util.CollectAxioms

noncomputable section
namespace PaperA

theorem quaternion_center (γ : Quaternion ℝ) (him : γ.re = 0)
    (hc : ∀ x, γ * x = x * γ) : γ = 0 := by
  let qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
  have hi := hc qi
  have hj := hc qj
  have himI : γ.imI = 0 := by
    have h := congrArg QuaternionAlgebra.imK hj
    simp only [Quaternion.imK_mul] at h
    simp [qj] at h
    nlinarith
  have himJ : γ.imJ = 0 := by
    have h := congrArg QuaternionAlgebra.imK hi
    simp only [Quaternion.imK_mul] at h
    simp [qi] at h
    nlinarith
  have himK : γ.imK = 0 := by
    have h := congrArg QuaternionAlgebra.imJ hi
    simp only [Quaternion.imJ_mul] at h
    simp [qi] at h
    nlinarith
  apply Quaternion.ext <;> assumption

end PaperA

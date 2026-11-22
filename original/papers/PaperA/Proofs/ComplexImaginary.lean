import Mathlib.Data.Complex.Basic
import Lean.Util.CollectAxioms

noncomputable section
namespace PaperA
theorem complex_imaginary (γ : ℂ) (h : γ.re = 0) : ∃! t : ℝ, γ = Complex.I*t := by
  refine ⟨γ.im, ?_, ?_⟩
  · apply Complex.ext
    · simp [Complex.mul_re, h]
    · simp [Complex.mul_im]
  · intro t ht
    have him := congrArg Complex.im ht
    simpa using him.symm

end PaperA

import PaperA.Spin
import Lean.Util.CollectAxioms

noncomputable section
namespace PaperA

theorem spin_rotation_converse {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (a b : Spin d) :
    spinMul (a.1, O a.2) (b.1, O b.2) = ((spinMul a b).1, O (spinMul a b).2) := by
  apply Prod.ext
  · simp only [spinMul, O.inner_map_map]
  · simp only [spinMul, map_add, map_smul]

end PaperA

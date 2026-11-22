import PaperA.SpinFieldV4

noncomputable section
namespace PaperA

theorem spin_field_bounded {d : ℕ} (A : AxisField d) : ∃ M : ℝ, ∀ v, ‖v‖ = 1 → ‖A.A v‖ ≤ M := by
  let s : Set (Vec d) := {v | ‖v‖ = 1}
  let f : Vec d → ℝ := fun v => ‖A.A v‖
  have hs : IsCompact s := by
    simpa [s, Metric.sphere, dist_eq_norm] using
      (isCompact_sphere (0 : Vec d) 1)
  have hf : ContinuousOn f s := by
    simpa [f, s] using A.continuous.norm
  obtain ⟨M, hM⟩ := hs.bddAbove_image hf
  refine ⟨M, fun v hv => ?_⟩
  have hmem : f v ∈ f '' s := ⟨v, hv, rfl⟩
  exact hM hmem

end PaperA

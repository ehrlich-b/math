import PaperA.Spin
import Lean.Util.CollectAxioms

noncomputable section
namespace PaperA

theorem spin_spectral {d : ℕ} (a : Spin d) (hn : a.2 ≠ 0) :
    let v := ‖a.2‖⁻¹ • a.2;
    ‖v‖ = 1 ∧ a = (a.1 + ‖a.2‖) • spinAtom v + (a.1 - ‖a.2‖) • spinAtom (-v) := by
  rcases a with ⟨α, x⟩
  change ‖‖x‖⁻¹ • x‖ = 1 ∧
    (α, x) = (α + ‖x‖) • spinAtom (‖x‖⁻¹ • x) +
      (α - ‖x‖) • spinAtom (-(‖x‖⁻¹ • x))
  have hx : x ≠ 0 := by simpa using hn
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    exact inv_mul_cancel₀ hr
  · apply Prod.ext
    · dsimp [spinAtom]
      ring
    · dsimp [spinAtom]
      have hcomb :
          (α + ‖x‖) • ((1 / 2 : ℝ) • (‖x‖⁻¹ • x)) +
            (α - ‖x‖) • ((1 / 2 : ℝ) • -(‖x‖⁻¹ • x)) =
              ‖x‖ • (‖x‖⁻¹ • x) := by
        simp only [smul_smul, smul_neg]
        module
      rw [hcomb]
      simp [hr]


end PaperA

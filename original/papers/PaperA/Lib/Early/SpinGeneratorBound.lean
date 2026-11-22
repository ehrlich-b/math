import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

noncomputable section
open NormedSpace intervalIntegral MeasureTheory

theorem uniform_exp_generator_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {ι : Type} (A : ι → E →L[ℝ] E)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v t, |t| < δ →
      ‖NormedSpace.exp (t • A v) - ContinuousLinearMap.id ℝ E‖ < ε) :
    ∃ M : ℝ, ∀ v, ‖A v‖ ≤ M := by
  obtain ⟨δ, hδ, hs⟩ := hsmall (1/2) (by norm_num)
  let s := δ / 2
  have hspos : 0 < s := by dsimp [s]; positivity
  refine ⟨1 / s, fun v => ?_⟩
  let T := A v
  let g : ℝ → (E →L[ℝ] E) := fun t => exp (t • T)
  have hg : Continuous g := continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) T t).continuousAt
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) s, ‖g t - 1‖ ≤ 1/2 := by
    intro t ht
    rw [Set.uIoc_of_le (le_of_lt hspos)] at ht
    have htδ : |t| < δ := by rw [abs_lt]; dsimp [s] at ht; constructor <;> linarith [ht.1, ht.2]
    simpa [g, T, ContinuousLinearMap.one_def] using le_of_lt (hs v t htδ)
  let I := ∫ t in (0 : ℝ)..s, g t
  have hdev : ‖I - s • 1‖ ≤ s/2 := by
    have hi : IntervalIntegrable g volume 0 s := hg.intervalIntegrable _ _
    have heq : I - s • 1 = ∫ t in (0 : ℝ)..s, (g t - 1) := by
      dsimp [I]
      rw [intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const]
      simp
    rw [heq]
    calc ‖∫ t in (0:ℝ)..s, (g t - 1)‖ ≤ 1/2 * |s - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = s / 2 := by rw [sub_zero, abs_of_pos hspos]; ring
  have hFTC : I * T = g s - 1 := by
    have hgi : IntervalIntegrable (fun t => g t * T) volume 0 s :=
      (hg.mul continuous_const).intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_exp_smul_const (𝕂 := ℝ) T t) hgi
    have hi : I * T = ∫ t in (0:ℝ)..s, g t * T := by
      dsimp [I]
      exact ((ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).flip T).intervalIntegral_comp_comm
        (hg.intervalIntegrable _ _) |>.symm
    rw [hi, h]
    simp [g]
  have hlower (z : E) : (s/2) * ‖z‖ ≤ ‖I z‖ := by
    have hn := (I - s • 1).le_opNorm z
    have hz : ‖(s • (1 : E →L[ℝ] E)) z‖ ≤ ‖I z‖ + ‖(I - s • 1) z‖ := by
      have h := norm_add_le (I z) (-((I - s • 1) z))
      simpa [norm_sub_rev] using h
    have hn' : ‖(I - s • 1) z‖ ≤ (s/2) * ‖z‖ :=
      hn.trans (mul_le_mul_of_nonneg_right hdev (norm_nonneg z))
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos hspos] at hz
    linarith
  have hu : ‖g s - 1‖ ≤ 1/2 := hb s (by rw [Set.uIoc_of_le (le_of_lt hspos)]; exact ⟨hspos, le_rfl⟩)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  have hl := hlower (T y)
  have hu' := (g s - 1).le_opNorm y
  have hm : ‖I (T y)‖ = ‖(g s - 1) y‖ := by rw [← hFTC]; rfl
  rw [hm] at hl
  have hu'' : ‖(g s - 1) y‖ ≤ (1/2) * ‖y‖ :=
    hu'.trans (mul_le_mul_of_nonneg_right hu (norm_nonneg y))
  dsimp [T] at hl
  have : ‖A v y‖ ≤ ‖y‖ / s := by
    apply (le_div_iff₀ hspos).2
    nlinarith
  simpa [div_eq_mul_inv, mul_comm] using this

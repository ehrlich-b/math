import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Normed.Operator.Basic

noncomputable section

namespace PaperA

theorem complex_structure_exp_aux {J : Type} [NormedAddCommGroup J] [NormedSpace ℝ J] [CompleteSpace J]
    (D : J →L[ℝ] J) (h : D.comp D = -ContinuousLinearMap.id ℝ J) (t : ℝ) :
    NormedSpace.exp (t • D) = Real.cos t • ContinuousLinearMap.id ℝ J + Real.sin t • D := by
  have hd : D ^ 2 = -(1 : J →L[ℝ] J) := by
    change D.comp D = -ContinuousLinearMap.id ℝ J at h
    exact h
  have hp (n : ℕ) : (-1 : J →L[ℝ] J) ^ n = ((-1 : ℝ) ^ n) • (1 : J →L[ℝ] J) := by
    rw [Algebra.smul_def, mul_one, map_pow]
    simp
  rw [NormedSpace.exp_eq_tsum ℝ]
  refine HasSum.tsum_eq ?_
  simp_rw [← NormedSpace.expSeries_apply_eq]
  refine HasSum.even_add_odd ?_ ?_
  · convert! (Real.hasSum_cos t).smul_const (1 : J →L[ℝ] J) using 1
    ext n : 1
    rw [NormedSpace.expSeries_apply_eq, smul_pow, show D ^ (2 * n) = (-1 : J →L[ℝ] J) ^ n by rw [pow_mul, hd]]
    rw [hp]
    simp [smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm]
  · convert! (Real.hasSum_sin t).smul_const D using 1
    ext n : 1
    rw [NormedSpace.expSeries_apply_eq, smul_pow, show D ^ (2 * n + 1) = (-1 : J →L[ℝ] J) ^ n * D by rw [pow_succ, pow_mul, hd]]
    rw [hp]
    simp [smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm]

end PaperA

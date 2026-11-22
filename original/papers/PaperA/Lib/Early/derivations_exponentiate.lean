import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.ExistUnique

open NormedSpace
variable {J : Type} [NormedAddCommGroup J] [NormedSpace ℝ J] [CompleteSpace J]
variable (B : J →L[ℝ] J →L[ℝ] J) (D : J →L[ℝ] J)
variable (hD : ∀ x y, D (B x y) = B (D x) y + B x (D y))

include hD in
theorem PaperA.exp_bilinear_of_derivation (x y : J) : ∀ t : ℝ, exp (t • D) (B x y) = B (exp (t • D) x) (exp (t • D) y) := by
  intro t
  have hflow (z : J) (s : ℝ) : HasDerivAt (fun u : ℝ => exp (u • D) z) (D (exp (s • D) z)) s := by
    have h := (hasDerivAt_exp_smul_const' D s).clm_apply (hasDerivAt_const s z)
    simpa using h
  have hproduct (s : ℝ) : HasDerivAt (fun u : ℝ => B (exp (u • D) x) (exp (u • D) y))
      (D (B (exp (s • D) x) (exp (s • D) y))) s := by
    rw [hD]
    exact ((B.hasFDerivAt.comp_hasDerivAt s (hflow x s)).clm_apply (hflow y s))
  have hu : (fun s : ℝ => exp (s • D) (B x y)) = (fun s : ℝ => B (exp (s • D) x) (exp (s • D) y)) := by
    apply ODE_solution_unique_univ (v := fun _ z => D z) (s := fun _ => Set.univ) (t₀ := 0)
    · intro s
      exact D.lipschitz.lipschitzOnWith
    · intro s
      exact ⟨hflow (B x y) s, Set.mem_univ _⟩
    · intro s
      exact ⟨hproduct s, Set.mem_univ _⟩
    · simp
  exact congrFun hu t

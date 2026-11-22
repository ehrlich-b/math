import PaperA.Definitions

noncomputable section
namespace PaperA

/-- Intertwining continuous operators also intertwines their exponential lines. -/
lemma spin_exp_intertwine {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (X Y : Vec d →L[ℝ] Vec d) (h : ∀ w, Y (O w) = O (X w))
    (t : ℝ) (w : Vec d) :
    NormedSpace.exp (t • Y) (O w) = O (NormedSpace.exp (t • X) w) := by
  -- The exponential intertwining API uses rational scalars.
  let : NormedAlgebra ℚ (Vec d →L[ℝ] Vec d) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  have hs : SemiconjBy O.toContinuousLinearEquiv.toContinuousLinearMap (t • X) (t • Y) := by
    apply ContinuousLinearMap.ext
    intro v
    change O (t • X v) = t • Y (O v)
    rw [O.map_smul, h v]
  have he := hs.exp_right
  exact (congrArg (fun f : Vec d →L[ℝ] Vec d => f w) he).symm

/-- Orthogonal transport preserves the normalized axis and every rotation branch. -/
lemma spin_rotation_transport {d : ℕ} (A B : AxisField d)
    (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (h : ∀ v, ‖v‖ = 1 → ∀ w, B.A (O v) (O w) = O (A.A v w))
    (a : Spin d) (w : Vec d) :
    spinRotation B (a.1, O a.2) (O w) = O (spinRotation A a w) := by
  classical
  have hz : O a.2 = 0 ↔ a.2 = 0 := by simp
  simp only [spinRotation, O.norm_map, hz]
  split_ifs with ha
  · rfl
  · have hn : a.2 ≠ 0 := fun hh => ha (Or.inl hh)
    have hu : ‖‖a.2‖⁻¹ • a.2‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]
    rw [← O.map_smul]
    exact spin_exp_intertwine O _ _ (h _ hu) _ w

/-- Covariance of the total spin-product formula, including the scalar branch. -/
lemma spin_product_transport {d : ℕ} (A B : AxisField d)
    (O : Vec d ≃ₗᵢ[ℝ] Vec d)
    (h : ∀ v, ‖v‖ = 1 → ∀ w, B.A (O v) (O w) = O (A.A v w))
    (a b : Spin d) :
    spinProduct B (a.1, O a.2) (b.1, O b.2) =
      ((spinProduct A a b).1, O (spinProduct A a b).2) := by
  classical
  have hz : O a.2 = 0 ↔ a.2 = 0 := by simp
  by_cases ha : a.2 = 0
  · simp [spinProduct, ha, map_smul]
  · have hOa : O a.2 ≠ 0 := fun hh => ha (hz.mp hh)
    have hu : ‖a.2‖⁻¹ • O a.2 = O (‖a.2‖⁻¹ • a.2) := (O.map_smul _ _).symm
    have hz' : inner ℝ (‖a.2‖⁻¹ • O a.2) (O b.2) =
        inner ℝ (‖a.2‖⁻¹ • a.2) b.2 := by rw [hu, O.inner_map_map]
    simp only [spinProduct, if_neg ha, if_neg hOa,
      O.norm_map, hz', O.inner_map_map]
    apply Prod.ext
    · rfl
    · dsimp only
      have hperp (z : ℝ) (u : Vec d) :
          O b.2 - z • O u = O (b.2 - z • u) := by simp
      rw [hu, hperp, spin_rotation_transport A B O h]
      simp only [map_add, map_smul]

end PaperA

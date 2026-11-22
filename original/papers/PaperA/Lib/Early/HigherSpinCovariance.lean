import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
namespace PaperA

/-- A skew operator fixing an axis sends every vector perpendicular to both. -/
theorem skew_axis_image_orthogonal {d : ℕ} (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (v w : EuclideanSpace ℝ (Fin d)) (hfix : T v = 0)
    (hskew : ∀ x y, inner ℝ x (T y) = -inner ℝ (T x) y) :
    inner ℝ v (T w) = 0 ∧ inner ℝ w (T w) = 0 := by
  constructor
  · rw [hskew, hfix]
    simp
  · have h := hskew w w
    have h' : inner ℝ w (T w) = -(inner ℝ w (T w)) := by
      simpa only [real_inner_comm (T w) w] using h
    linarith
end PaperA



namespace PaperA
/-- The missing auxiliary direction for a determinant-one half-turn. -/
theorem exists_orthogonal_fourth {d : ℕ} (hd : 4 ≤ d)
    (v w z : EuclideanSpace ℝ (Fin d)) :
    ∃ q : EuclideanSpace ℝ (Fin d), q ≠ 0 ∧
      inner ℝ v q = 0 ∧ inner ℝ w q = 0 ∧ inner ℝ z q = 0 := by
  classical
  let K := Submodule.span ℝ ({v, w, z} : Set (EuclideanSpace ℝ (Fin d)))
  have hdim : Module.finrank ℝ K ≤ 3 := by
    calc
      _ ≤ ({v, w, z} : Set (EuclideanSpace ℝ (Fin d))).toFinset.card :=
        finrank_span_le_card _
      _ ≤ 3 := by simpa using (Finset.card_le_three (a := v) (b := w) (c := z))
  have hproper : K ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hdim
    simp at hdim
    omega
  have hnonzero : Kᗮ ≠ ⊥ := by
    intro h
    exact hproper (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnonzero
  refine ⟨q, hq0, ?_, ?_, ?_⟩ <;>
    rw [real_inner_comm] <;>
    apply Submodule.inner_left_of_mem_orthogonal _ hq <;>
    apply Submodule.subset_span <;> simp
end PaperA

namespace PaperA
theorem stabilizer_rotation {d : ℕ} (hd : 4 ≤ d)
    (v w z : EuclideanSpace ℝ (Fin d))
    (hvz : inner ℝ v z = 0) (hwz : inner ℝ w z = 0) :
    ∃ O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      LinearMap.det O.toLinearEquiv.toLinearMap = 1 ∧ O v = v ∧ O w = w ∧ O z = -z := by
  by_cases hz : z = 0
  · subst z
    exact ⟨LinearIsometryEquiv.refl ℝ _, by simp, by simp, by simp, by simp⟩
  obtain ⟨q, hq, hvq, hwq, hzq⟩ := exists_orthogonal_fourth hd v w z
  let Rz := (Submodule.span ℝ {z})ᗮ.reflection
  let Rq := (Submodule.span ℝ {q})ᗮ.reflection
  refine ⟨Rz.trans Rq, ?_, ?_, ?_, ?_⟩
  · change LinearMap.det (Rq.toLinearMap.comp Rz.toLinearMap) = 1
    rw [LinearMap.det_comp]
    change LinearMap.det ((Submodule.span ℝ {q})ᗮ.reflection.toLinearMap) *
      LinearMap.det ((Submodule.span ℝ {z})ᗮ.reflection.toLinearMap) = 1
    rw [Submodule.det_reflection, Submodule.det_reflection,
      Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal,
      finrank_span_singleton hq, finrank_span_singleton hz]
    norm_num
  · have h₁ : Rz v = v := by
      apply Submodule.reflection_mem_subspace_eq_self
      simpa [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm] using hvz
    have h₂ : Rq v = v := by
      apply Submodule.reflection_mem_subspace_eq_self
      simpa [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm] using hvq
    simpa [h₁] using h₂
  · have h₁ : Rz w = w := by
      apply Submodule.reflection_mem_subspace_eq_self
      simpa [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm] using hwz
    have h₂ : Rq w = w := by
      apply Submodule.reflection_mem_subspace_eq_self
      simpa [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm] using hwq
    simpa [h₁] using h₂
  · have h₁ : Rz z = -z := Submodule.reflection_orthogonalComplement_singleton_eq_neg z
    have h₂ : Rq z = z := by
      apply Submodule.reflection_mem_subspace_eq_self
      simpa [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm] using hzq
    simpa [h₁, map_neg, h₂]
end PaperA

namespace PaperA
/-- A skew axis-fixing endomorphism invariant under the axis stabilizer is zero. -/
theorem skew_covariant_zero {d : ℕ} (hd : 4 ≤ d)
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) (hfix : T v = 0)
    (hskew : ∀ x y, inner ℝ x (T y) = -inner ℝ (T x) y)
    (hinv : ∀ O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      LinearMap.det O.toLinearEquiv.toLinearMap = 1 → O v = v →
      ∀ w, T (O w) = O (T w)) : T = 0 := by
  apply ContinuousLinearMap.ext
  intro w
  change T w = 0
  obtain ⟨hv, hw⟩ := skew_axis_image_orthogonal T v w hfix hskew
  obtain ⟨O, hdet, hOv, hOw, hOz⟩ := stabilizer_rotation hd v w (T w) hv hw
  have h := hinv O hdet hOv w
  rw [hOw, hOz] at h
  have hz : inner ℝ (T w) (T w) = 0 := by
    have hi := congrArg (fun x => inner ℝ (T w) x) h
    simp only [inner_neg_right] at hi
    linarith
  exact inner_self_eq_zero.mp hz
end PaperA

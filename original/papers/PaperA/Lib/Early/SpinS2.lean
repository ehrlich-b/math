import PaperA.Definitions
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open scoped Topology
namespace PaperA

private theorem normalized_norm {d : ℕ} (x : Vec d) (hx : x ≠ 0) :
    ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem spin_exp_norm {d : ℕ} (A : AxisField d) (v : Vec d) (hv : ‖v‖ = 1)
    (t : ℝ) (x : Vec d) : ‖NormedSpace.exp (t • A.A v) x‖ = ‖x‖ := by
  let : NormedAlgebra ℚ (Vec d →L[ℝ] Vec d) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hskew : star (t • A.A v) = -(t • A.A v) := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply ContinuousLinearMap.ext
    intro z
    apply ext_inner_right ℝ
    intro y
    simp only [ContinuousLinearMap.adjoint_inner_left, smul_apply,
      neg_apply, real_inner_smul_left, real_inner_smul_right,
      inner_neg_left]
    rw [A.skew v hv]
    ring
  have hmem : t • A.A v ∈ skewAdjoint (Vec d →L[ℝ] Vec d) := hskew
  have hu : NormedSpace.exp (t • A.A v) ∈ unitary (Vec d →L[ℝ] Vec d) :=
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hmem
  exact ContinuousLinearMap.norm_map_of_mem_unitary hu x

theorem spinRotation_norm {d : ℕ} (A : AxisField d) (a : Spin d) (x : Vec d) :
    ‖spinRotation A a x‖ = ‖x‖ := by
  unfold spinRotation
  split_ifs with h
  · rfl
  · exact spin_exp_norm A _ (normalized_norm _ (not_or.mp h).1) _ x

private def axis {d : ℕ} (a : Spin d) : Vec d := ‖a.2‖⁻¹ • a.2
private def projection {d : ℕ} (a b : Spin d) : Vec d :=
  (inner ℝ (axis a) b.2) • axis a
private def weight {d : ℕ} (a : Spin d) : ℝ := Real.sqrt (a.1^2 - ‖a.2‖^2)

private theorem axis_norm_le {d : ℕ} (a : Spin d) : ‖axis a‖ ≤ 1 := by
  by_cases h : a.2 = 0
  · simp [axis, h]
  · exact (normalized_norm _ h).le

private theorem projection_norm_le {d : ℕ} (a b : Spin d) :
    ‖projection a b‖ ≤ ‖b.2‖ := by
  have hu := axis_norm_le a
  calc
    ‖projection a b‖ = |inner ℝ (axis a) b.2| * ‖axis a‖ := by
      rw [projection, norm_smul, Real.norm_eq_abs]
    _ ≤ (‖axis a‖ * ‖b.2‖) * ‖axis a‖ :=
      mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
    _ ≤ (1 * ‖b.2‖) * 1 := by gcongr
    _ = ‖b.2‖ := by ring

private theorem transverse_norm_le {d : ℕ} (A : AxisField d) (a b : Spin d) :
    ‖spinRotation A a (b.2 - projection a b)‖ ≤ 2 * ‖b.2‖ := by
  rw [spinRotation_norm]
  calc
    ‖b.2 - projection a b‖ ≤ ‖b.2‖ + ‖projection a b‖ := norm_sub_le _ _
    _ ≤ 2 * ‖b.2‖ := by linarith [projection_norm_le a b]

private theorem spinProduct_formula {d : ℕ} (A : AxisField d) (a b : Spin d)
    (ha : spinPositive a) : spinProduct A a b =
      (a.1*b.1 + inner ℝ a.2 b.2,
       b.1 • a.2 + a.1 • projection a b +
         weight a • spinRotation A a (b.2 - projection a b)) := by
  by_cases hx : a.2 = 0
  · have hs : 0 ≤ a.1 := by simpa [spinPositive, hx] using ha
    apply Prod.ext <;>
      simp [spinProduct, hx, projection, axis, weight, Real.sqrt_sq hs, spinRotation, smul_eq_mul]
  · simp only [spinProduct, if_neg hx, projection, axis, weight, smul_smul]
    simp only [mul_assoc]

private theorem weight_continuous {d : ℕ} : Continuous (weight : Spin d → ℝ) := by
  unfold weight
  fun_prop

private theorem axis_continuousAt {d : ℕ} (a : Spin d) (hx : a.2 ≠ 0) :
    ContinuousAt axis a := by
  exact ((continuous_snd.norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)).smul
    continuous_snd.continuousAt)

private theorem projection_continuousAt {d : ℕ} (a b : Spin d) (hx : a.2 ≠ 0) :
    ContinuousAt (fun a => projection a b) a := by
  exact ((axis_continuousAt a hx).inner (𝕜 := ℝ) continuousAt_const).smul (axis_continuousAt a hx)

private theorem spinRotation_continuousAt {d : ℕ} (A : AxisField d) (a : Spin d)
    (hx : a.2 ≠ 0) (hs : ‖a.2‖ < a.1) : ContinuousAt (spinRotation A) a := by
  let : NormedAlgebra ℚ (Vec d →L[ℝ] Vec d) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hu := axis_continuousAt a hx
  have hf : ContinuousAt (fun x => A.A (axis x)) a := by
    have hA : Filter.Tendsto A.A (𝓝[{v | ‖v‖ = 1}] (axis a))
        (𝓝 (A.A (axis a))) := A.continuous _ (normalized_norm _ hx)
    apply hA.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hu, ?_⟩
    filter_upwards [continuous_snd.continuousAt.eventually_ne hx] with x hx
    exact normalized_norm _ hx
  have ht : ContinuousAt (fun x : Spin d =>
      Real.log ((x.1 + ‖x.2‖) / (x.1 - ‖x.2‖))) a := by
    apply ContinuousAt.log
    · exact (continuous_fst.add continuous_snd.norm).continuousAt.div
        (continuous_fst.sub continuous_snd.norm).continuousAt (by linarith)
    · exact ne_of_gt (div_pos (by linarith [norm_nonneg a.2]) (sub_pos.mpr hs))
  have he := NormedSpace.exp_continuous.continuousAt.comp (ht.smul hf)
  apply he.congr
  filter_upwards [continuous_snd.continuousAt.eventually_ne hx,
    (isOpen_lt continuous_snd.norm continuous_fst).mem_nhds hs] with x hx hs
  simp only [spinRotation, if_neg (not_or.mpr ⟨hx, not_le.mpr hs⟩), axis]
  rfl

private theorem spinRotation_continuousAt_scalar {d : ℕ} (A : AxisField d)
    (hbounded : ∃ M : ℝ, ∀ v, ‖v‖ = 1 → ‖A.A v‖ ≤ M)
    (a : Spin d) (hx : a.2 = 0) (hs : 0 < a.1) : ContinuousAt (spinRotation A) a := by
  let : NormedAlgebra ℚ (Vec d →L[ℝ] Vec d) := NormedAlgebra.restrictScalars ℚ ℝ _
  obtain ⟨M, hM⟩ := hbounded
  let t : Spin d → ℝ := fun x => Real.log ((x.1 + ‖x.2‖) / (x.1 - ‖x.2‖))
  have ht : ContinuousAt t a := by
    apply ContinuousAt.log
    · exact (continuous_fst.add continuous_snd.norm).continuousAt.div
        (continuous_fst.sub continuous_snd.norm).continuousAt (by simpa [hx] using hs.ne')
    · simp [hx, hs.ne']
  have ht0 : t a = 0 := by simp [t, hx, hs.ne']
  -- The axis need not converge: its generator is uniformly bounded on the sphere.
  let g : Spin d → (Vec d →L[ℝ] Vec d) :=
    fun x => if x.2 = 0 then 0 else t x • A.A (axis x)
  have hg : Filter.Tendsto g (𝓝 a) (𝓝 0) := by
    apply squeeze_zero_norm (a := fun x => ‖t x‖ * max M 0)
    · intro x
      by_cases hx : x.2 = 0
      · simp only [g, if_pos hx, norm_zero]
        exact mul_nonneg (norm_nonneg _) (le_max_right M 0)
      · change ‖(if x.2 = 0 then 0 else t x • A.A (axis x))‖ ≤ _
        rw [if_neg hx, norm_smul]
        exact mul_le_mul_of_nonneg_left
          ((hM _ (normalized_norm _ hx)).trans (le_max_left M 0)) (norm_nonneg _)
    · simpa [ht0] using ht.tendsto.norm.mul_const (max M 0)
  have he : Filter.Tendsto (fun x => NormedSpace.exp (g x)) (𝓝 a)
      (𝓝 (ContinuousLinearMap.id ℝ (Vec d))) := by
    simpa only [NormedSpace.exp_zero, ContinuousLinearMap.one_def] using hg.exp
  have hnear : ∀ᶠ x : Spin d in 𝓝 a, ‖x.2‖ < x.1 :=
    (isOpen_lt continuous_snd.norm continuous_fst).mem_nhds (by simpa [hx] using hs)
  have hval : spinRotation A a = ContinuousLinearMap.id ℝ (Vec d) := by
    simp [spinRotation, hx]
  rw [ContinuousAt, hval]
  apply he.congr'
  filter_upwards [hnear] with x hsx
  by_cases hxx : x.2 = 0
  · simp [g, hxx, spinRotation, ContinuousLinearMap.one_def]
  · simp [g, hxx, spinRotation, not_le.mpr hsx, t, axis]

private theorem transverse_bounded {d : ℕ} (b : Spin d) (l : Filter (Spin d)) :
    Filter.IsBoundedUnder (· ≤ ·) l
      (fun a => ‖b.2 - projection a b‖) := by
  exact Filter.isBoundedUnder_of ⟨2 * ‖b.2‖, fun a =>
    (norm_sub_le _ _).trans (by linarith [projection_norm_le a b])⟩

private theorem projection_bounded {d : ℕ} (b : Spin d) (l : Filter (Spin d)) :
    Filter.IsBoundedUnder (· ≤ ·) l (fun a => ‖projection a b‖) :=
  Filter.isBoundedUnder_of ⟨‖b.2‖, fun a => projection_norm_le a b⟩

/-- This isolates the two vanishing errors at a positive scalar first effect. -/
private theorem spinProduct_snd_rewrite {d : ℕ} (A : AxisField d) (a b : Spin d)
    (ha : spinPositive a) : (spinProduct A a b).2 =
      b.1 • a.2 + a.1 • b.2 +
      (weight a - a.1) • (b.2 - projection a b) +
      weight a • ((spinRotation A a - ContinuousLinearMap.id ℝ (Vec d))
        (b.2 - projection a b)) := by
  rw [spinProduct_formula A a b ha]
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    smul_sub, sub_smul]
  module

/-- The singular value is supplied by the rank-one formula, independently of the rotation. -/
private theorem singular_snd_of_formula {d : ℕ} (A : AxisField d)
    (hformula : ∀ (v : Vec d), ‖v‖ = 1 → ∀ lam : ℝ, 0 < lam → ∀ b : Spin d,
      spinProduct A (lam • spinAtom v) b =
        (lam * (b.1 + inner ℝ v b.2)) • spinAtom v)
    (a b : Spin d) (hx : a.2 ≠ 0) (hs : a.1 = ‖a.2‖) :
    (spinProduct A a b).2 = b.1 • a.2 + a.1 • projection a b := by
  have hscale : a.1 • axis a = a.2 := by
    rw [hs, axis, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have ha : a = (2 * a.1) • spinAtom (axis a) := by
    apply Prod.ext
    · change a.1 = (2 * a.1) * (1 / 2 : ℝ)
      ring
    · change a.2 = (2 * a.1) • ((1 / 2 : ℝ) • axis a)
      rw [smul_smul, show (2 * a.1) * (1 / 2 : ℝ) = a.1 by ring, hscale]
  have hlam : 0 < 2 * a.1 := by rw [hs]; positivity
  have h := congrArg Prod.snd (hformula (axis a) (normalized_norm _ hx) (2 * a.1) hlam b)
  rw [← ha] at h
  rw [h]
  change (2 * a.1 * (b.1 + inner ℝ (axis a) b.2)) • ((1 / 2 : ℝ) • axis a) = _
  calc
    _ = b.1 • (a.1 • axis a) + a.1 • projection a b := by
      simp only [projection, smul_smul]
      module
    _ = b.1 • a.2 + a.1 • projection a b := by rw [hscale]

/-- Continuity follows from the compact-sphere bound and the singular rank-one value. -/
theorem spin_s2_of_bounded {d : ℕ} (A : AxisField d)
    (hbounded : ∃ M : ℝ, ∀ v, ‖v‖ = 1 → ‖A.A v‖ ≤ M)
    (hsingular : ∀ (v : Vec d), ‖v‖ = 1 → ∀ lam : ℝ, 0 < lam → ∀ b : Spin d,
      spinProduct A (lam • spinAtom v) b =
        (lam * (b.1 + inner ℝ v b.2)) • spinAtom v)
    (b : Spin d) : ContinuousOn (fun a => spinProduct A a b) {a | spinEffect a} := by
  intro a ha
  have hpos : spinPositive a := ha.1
  have hs : 0 ≤ a.1 := (norm_nonneg a.2).trans hpos
  have heffects : ∀ᶠ x in 𝓝[{x | spinEffect x}] a, spinPositive x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx.1
  have hweight : Filter.Tendsto (weight : Spin d → ℝ)
      (𝓝[{x | spinEffect x}] a) (𝓝 (weight a)) := weight_continuous.continuousWithinAt
  have hscalar : Filter.Tendsto (fun x : Spin d => x.1)
      (𝓝[{x | spinEffect x}] a) (𝓝 a.1) := continuous_fst.continuousWithinAt
  have hvector : Filter.Tendsto (fun x : Spin d => b.1 • x.2)
      (𝓝[{x | spinEffect x}] a) (𝓝 (b.1 • a.2)) :=
    (continuous_snd.const_smul b.1).continuousWithinAt
  have hfst : ContinuousAt (fun x : Spin d => x.1 * b.1 + inner ℝ x.2 b.2) a := by
    fun_prop
  have hfsteq : (spinProduct A a b).1 = a.1 * b.1 + inner ℝ a.2 b.2 := by
    rw [spinProduct_formula A a b hpos]
  have hfstlim : Filter.Tendsto (fun x => (spinProduct A x b).1)
      (𝓝[{x | spinEffect x}] a) (𝓝 (spinProduct A a b).1) := by
    rw [hfsteq]
    apply hfst.continuousWithinAt.tendsto.congr'
    filter_upwards [heffects] with x hx
    rw [spinProduct_formula A x b hx]
  suffices hsndlim : Filter.Tendsto (fun x => (spinProduct A x b).2)
      (𝓝[{x | spinEffect x}] a) (𝓝 (spinProduct A a b).2) by
    exact hfstlim.prodMk_nhds hsndlim
  by_cases hx : a.2 = 0
  · by_cases hzero : a.1 = 0
    · have hw : weight a = 0 := by simp [weight, hx, hzero]
      have hs0 : Filter.Tendsto (fun x : Spin d => x.1)
          (𝓝[{x | spinEffect x}] a) (𝓝 0) := by
        simpa [hzero] using hscalar
      have hproj := hs0.zero_smul_isBoundedUnder_le
        (projection_bounded b (𝓝[{x | spinEffect x}] a))
      have htrans : Filter.Tendsto
          (fun x => weight x • spinRotation A x (b.2 - projection x b))
          (𝓝[{x | spinEffect x}] a) (𝓝 0) := by
        apply Filter.Tendsto.zero_smul_isBoundedUnder_le
          (by simpa [hw] using hweight)
        exact Filter.isBoundedUnder_of ⟨2 * ‖b.2‖, fun x => transverse_norm_le A x b⟩
      have hxlim : Filter.Tendsto (fun x : Spin d => b.1 • x.2)
          (𝓝[{x | spinEffect x}] a) (𝓝 0) := by
        simpa [hx] using hvector
      have hlim := (hxlim.add hproj).add htrans
      have hz : (spinProduct A a b).2 = 0 := by simp [spinProduct, hx, hzero]
      rw [hz]
      simp only [add_zero] at hlim
      apply hlim.congr'
      filter_upwards [heffects] with x hx
      rw [spinProduct_formula A x b hx]
    · have hrot := spinRotation_continuousAt_scalar A hbounded a hx (lt_of_le_of_ne hs (Ne.symm hzero))
      have hw : weight a = a.1 := by simp [weight, hx, Real.sqrt_sq hs]
      have hdiff : Filter.Tendsto (fun x : Spin d => weight x - x.1)
          (𝓝[{x | spinEffect x}] a) (𝓝 0) := by
        simpa [hw] using hweight.sub hscalar
      have hterm := hdiff.zero_smul_isBoundedUnder_le
        (transverse_bounded b (𝓝[{x | spinEffect x}] a))
      have hrval : spinRotation A a = ContinuousLinearMap.id ℝ (Vec d) := by
        simp [spinRotation, hx]
      have hrot0 : Filter.Tendsto (fun x => ‖spinRotation A x - ContinuousLinearMap.id ℝ (Vec d)‖)
          (𝓝[{x | spinEffect x}] a) (𝓝 0) := by
        have hrotDiff : ContinuousAt (fun x => spinRotation A x -
            ContinuousLinearMap.id ℝ (Vec d)) a := hrot.sub continuousAt_const
        simpa [hrval] using (hrotDiff.norm.continuousWithinAt (s := {x | spinEffect x})).tendsto
      have herr : Filter.Tendsto (fun x =>
          (spinRotation A x - ContinuousLinearMap.id ℝ (Vec d)) (b.2 - projection x b))
          (𝓝[{x | spinEffect x}] a) (𝓝 0) := by
        apply squeeze_zero_norm (a := fun x =>
          ‖spinRotation A x - ContinuousLinearMap.id ℝ (Vec d)‖ * (2 * ‖b.2‖))
        · intro x
          exact ((spinRotation A x - ContinuousLinearMap.id ℝ (Vec d)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left
              ((norm_sub_le _ _).trans (by linarith [projection_norm_le x b])) (norm_nonneg _))
        · simpa using hrot0.mul_const (2 * ‖b.2‖)
      have hlast := hweight.smul herr
      have hbase : ContinuousAt (fun x : Spin d => b.1 • x.2 + x.1 • b.2) a := by fun_prop
      have hlim := (hbase.continuousWithinAt.tendsto.add hterm).add hlast
      have hv : (spinProduct A a b).2 = b.1 • a.2 + a.1 • b.2 := by
        simp [spinProduct, hx]
      rw [hv]
      simp only [add_zero, smul_zero] at hlim
      apply hlim.congr'
      filter_upwards [heffects] with x hx
      rw [spinProduct_snd_rewrite A x b hx]
  · have hu := projection_continuousAt a b hx
    by_cases hsing : a.1 = ‖a.2‖
    · have hw : weight a = 0 := by simp [weight, hsing]
      have htrans : Filter.Tendsto
          (fun x => weight x • spinRotation A x (b.2 - projection x b))
          (𝓝[{x | spinEffect x}] a) (𝓝 0) := by
        apply Filter.Tendsto.zero_smul_isBoundedUnder_le
          (by simpa [hw] using hweight)
        exact Filter.isBoundedUnder_of ⟨2 * ‖b.2‖, fun x => transverse_norm_le A x b⟩
      have hbase : ContinuousAt (fun x : Spin d => b.1 • x.2 + x.1 • projection x b) a :=
        (continuous_snd.continuousAt.const_smul b.1).add (continuous_fst.continuousAt.smul hu)
      have hlim := hbase.continuousWithinAt.tendsto.add htrans
      have hv := singular_snd_of_formula A hsingular a b hx hsing
      rw [hv]
      simp only [add_zero] at hlim
      apply hlim.congr'
      filter_upwards [heffects] with x hx
      rw [spinProduct_formula A x b hx]
    · have hrot := spinRotation_continuousAt A a hx (lt_of_le_of_ne hpos (Ne.symm hsing))
      have hformula : ContinuousAt (fun x : Spin d =>
          b.1 • x.2 + x.1 • projection x b +
          weight x • spinRotation A x (b.2 - projection x b)) a := by
        exact ((continuous_snd.continuousAt.const_smul b.1).add
          (continuous_fst.continuousAt.smul hu)).add
          (weight_continuous.continuousAt.smul
            (hrot.clm_apply (continuousAt_const.sub hu)))
      rw [spinProduct_formula A a b hpos]
      apply hformula.continuousWithinAt.tendsto.congr'
      filter_upwards [heffects] with x hx
      rw [spinProduct_formula A x b hx]

end PaperA

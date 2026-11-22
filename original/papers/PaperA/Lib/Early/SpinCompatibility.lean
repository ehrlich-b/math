import PaperA.Definitions
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-! Rotation invariants and the collinearity criterion for the spin product. -/

noncomputable section
namespace PaperA
namespace SpinCompatibility

variable {d : ℕ}

lemma exp_apply_deriv (T : Vec d →L[ℝ] Vec d) (x : Vec d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • T) x)
      (T (NormedSpace.exp (t • T) x)) t := by
  simpa using (hasDerivAt_exp_smul_const' T t).clm_apply (hasDerivAt_const t x)

lemma exp_norm (T : Vec d →L[ℝ] Vec d)
    (hT : ∀ x y, inner ℝ x (T y) = -inner ℝ (T x) y) (x : Vec d) (t : ℝ) :
    ‖NormedSpace.exp (t • T) x‖ = ‖x‖ := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => inner ℝ
      (NormedSpace.exp (r • T) x) (NormedSpace.exp (r • T) x)) 0 s := by
    apply ((exp_apply_deriv T x s).inner ℝ (exp_apply_deriv T x s)).congr_deriv
    have h := hT (NormedSpace.exp (s • T) x) (NormedSpace.exp (s • T) x)
    linarith
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  have h0 : NormedSpace.exp ((0 : ℝ) • T) x = x := by
    have hz : (0 : ℝ) • T = 0 := zero_smul ℝ T
    rw [hz, NormedSpace.exp_zero]
    rfl
  rw [h0] at h
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (NormedSpace.exp (t • T) x), norm_nonneg x]

lemma exp_inner (T : Vec d →L[ℝ] Vec d)
    (hT : ∀ x y, inner ℝ x (T y) = -inner ℝ (T x) y)
    (v : Vec d) (hv : T v = 0) (x : Vec d) (t : ℝ) :
    inner ℝ (NormedSpace.exp (t • T) x) v = inner ℝ x v := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ =>
      inner ℝ (NormedSpace.exp (r • T) x) v) 0 s := by
    apply ((exp_apply_deriv T x s).inner ℝ (hasDerivAt_const s v)).congr_deriv
    have h := hT (NormedSpace.exp (s • T) x) v
    simp only [hv, inner_zero_right] at h
    simpa only [inner_zero_right, zero_add] using (neg_eq_zero.mp h.symm)
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  have h0 : NormedSpace.exp ((0 : ℝ) • T) x = x := by
    have hz : (0 : ℝ) • T = 0 := zero_smul ℝ T
    rw [hz, NormedSpace.exp_zero]
    rfl
  rw [h0] at h
  exact h

lemma unit_axis (p : Vec d) (hp : p ≠ 0) : ‖‖p‖⁻¹ • p‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg p)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)

lemma rotation_norm (A : AxisField d) (a : Spin d) (x : Vec d) :
    ‖spinRotation A a x‖ = ‖x‖ := by
  unfold spinRotation
  split_ifs with h
  · rfl
  · exact exp_norm _ (A.skew _ (unit_axis _ (not_or.mp h).1)) _ _

lemma rotation_isometry (A : AxisField d) (a : Spin d) : Isometry (spinRotation A a) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, rotation_norm]

lemma rotation_inner (A : AxisField d) (a : Spin d) (ha : a.2 ≠ 0) (x : Vec d) :
    inner ℝ (spinRotation A a x) (‖a.2‖⁻¹ • a.2) = inner ℝ x (‖a.2‖⁻¹ • a.2) := by
  unfold spinRotation
  split_ifs
  · rfl
  · exact exp_inner _ (A.skew _ (unit_axis _ ha)) _ (A.fixes _ (unit_axis _ ha)) _ _

def axis (p : Vec d) : Vec d := ‖p‖⁻¹ • p

def perp (p x : Vec d) : Vec d := x - inner ℝ (axis p) x • axis p

lemma axis_norm (p : Vec d) (hp : p ≠ 0) : ‖axis p‖ = 1 := unit_axis p hp

lemma axis_inner (p : Vec d) (hp : p ≠ 0) : inner ℝ (axis p) (axis p) = 1 := by
  rw [real_inner_self_eq_norm_sq, axis_norm p hp, one_pow]

lemma axis_scale (p : Vec d) : ‖p‖ • axis p = p := by
  by_cases hp : p = 0
  · simp [hp, axis]
  · simp [axis, smul_smul, norm_ne_zero_iff.mpr hp]

lemma rotation_fixes_axis (A : AxisField d) (a : Spin d) (ha : a.2 ≠ 0) :
    spinRotation A a (axis a.2) = axis a.2 := by
  have h := norm_sub_sq_real (spinRotation A a (axis a.2)) (axis a.2)
  rw [rotation_norm, show inner ℝ (spinRotation A a (axis a.2)) (axis a.2) =
    inner ℝ (axis a.2) (axis a.2) from rotation_inner A a ha _,
    real_inner_self_eq_norm_sq] at h
  have hn : ‖spinRotation A a (axis a.2) - axis a.2‖ = 0 := by
    nlinarith [norm_nonneg (spinRotation A a (axis a.2) - axis a.2)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

lemma rotation_fixes (A : AxisField d) (a : Spin d) : spinRotation A a a.2 = a.2 := by
  by_cases ha : a.2 = 0
  · simp [ha]
  · calc
      _ = spinRotation A a (‖a.2‖ • axis a.2) := by rw [axis_scale]
      _ = ‖a.2‖ • axis a.2 := by rw [map_smul, rotation_fixes_axis A a ha]
      _ = a.2 := axis_scale _

lemma perp_inner_axis (p x : Vec d) (hp : p ≠ 0) :
    inner ℝ (perp p x) (axis p) = 0 := by
  rw [perp, inner_sub_left, real_inner_smul_left, axis_inner p hp, mul_one,
    real_inner_comm x (axis p), sub_self]

lemma perp_inner_self (p x : Vec d) (hp : p ≠ 0) :
    inner ℝ (perp p x) x = ‖perp p x‖ ^ 2 := by
  have h := perp_inner_axis p x hp
  calc
    inner ℝ (perp p x) x = inner ℝ (perp p x)
        (perp p x + inner ℝ (axis p) x • axis p) := by rw [perp]; congr 1; module
    _ = ‖perp p x‖ ^ 2 := by
      rw [inner_add_right, real_inner_smul_right, h, mul_zero, add_zero,
        real_inner_self_eq_norm_sq]

lemma perp_smul (p x : Vec d) (r : ℝ) : perp p (r • x) = r • perp p x := by
  simp only [perp, real_inner_smul_right]
  module

lemma perp_same (p : Vec d) : perp p p = 0 := by
  by_cases hp : p = 0
  · simp [perp, axis, hp]
  · have h : inner ℝ (axis p) p = ‖p‖ := by
      rw [axis, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    rw [perp, h, axis_scale, sub_self]

lemma perp_rotation_inner (A : AxisField d) (a : Spin d) (ha : a.2 ≠ 0) (x : Vec d) :
    inner ℝ (spinRotation A a (perp a.2 x)) (axis a.2) = 0 := by
  change inner ℝ (spinRotation A a (perp a.2 x)) (‖a.2‖⁻¹ • a.2) = 0
  rw [rotation_inner A a ha]
  exact perp_inner_axis a.2 x ha

lemma rotation_perp_bound (A : AxisField d) (a : Spin d) (ha : a.2 ≠ 0) (x : Vec d) :
    inner ℝ (spinRotation A a (perp a.2 x)) x ≤ ‖perp a.2 x‖ ^ 2 := by
  have hzero := perp_rotation_inner A a ha x
  have heq : inner ℝ (spinRotation A a (perp a.2 x)) x =
      inner ℝ (spinRotation A a (perp a.2 x)) (perp a.2 x) := by
    change inner ℝ (spinRotation A a (perp a.2 x)) x =
      inner ℝ (spinRotation A a (perp a.2 x)) (x - inner ℝ (axis a.2) x • axis a.2)
    rw [inner_sub_right, real_inner_smul_right, hzero, mul_zero, sub_zero]
  rw [heq]
  calc
    _ ≤ ‖spinRotation A a (perp a.2 x)‖ * ‖perp a.2 x‖ := real_inner_le_norm _ _
    _ = ‖perp a.2 x‖ ^ 2 := by rw [rotation_norm]; ring

lemma product_snd (A : AxisField d) (a b : Spin d) (ha : a.2 ≠ 0) :
    (spinProduct A a b).2 = b.1 • a.2 + a.1 • b.2 +
      (-a.1 • perp a.2 b.2 + Real.sqrt (a.1^2 - ‖a.2‖^2) •
        spinRotation A a (perp a.2 b.2)) := by
  simp only [spinProduct, if_neg ha, perp, axis]
  module

lemma sqrt_lt_scalar (b : Spin d) (hb : spinEffect b) (hnb : b.2 ≠ 0) :
    Real.sqrt (b.1^2 - ‖b.2‖^2) < b.1 := by
  have hn : 0 < ‖b.2‖ := norm_pos_iff.mpr hnb
  have hp : ‖b.2‖ ≤ b.1 := hb.1
  have hnon : 0 ≤ b.1^2 - ‖b.2‖^2 := by nlinarith
  have hs := Real.sq_sqrt hnon
  have hpos := Real.sqrt_nonneg (b.1^2 - ‖b.2‖^2)
  nlinarith

lemma compatible_implies_collinear (A : AxisField d) (a b : Spin d)
    (hb : spinEffect b) (hna : a.2 ≠ 0) (hnb : b.2 ≠ 0)
    (h : spinProduct A a b = spinProduct A b a) : ∃ r : ℝ, a.2 = r • b.2 := by
  have hv := congrArg Prod.snd h
  rw [product_snd A a b hna, product_snd A b a hnb] at hv
  -- Remove the common symmetric vector part before pairing with the first axis.
  have hc : -a.1 • perp a.2 b.2 + Real.sqrt (a.1^2 - ‖a.2‖^2) •
      spinRotation A a (perp a.2 b.2) =
      -b.1 • perp b.2 a.2 + Real.sqrt (b.1^2 - ‖b.2‖^2) •
      spinRotation A b (perp b.2 a.2) := by
    apply add_left_cancel (a := b.1 • a.2 + a.1 • b.2)
    simpa only [add_comm, add_left_comm, add_assoc] using hv
  have hx : inner ℝ (perp a.2 b.2) a.2 = 0 := by
    calc
      _ = inner ℝ (perp a.2 b.2) (‖a.2‖ • axis a.2) := by rw [axis_scale]
      _ = 0 := by rw [real_inner_smul_right, perp_inner_axis _ _ hna, mul_zero]
  have hrx : inner ℝ (spinRotation A a (perp a.2 b.2)) a.2 = 0 := by
    calc
      _ = inner ℝ (spinRotation A a (perp a.2 b.2)) (‖a.2‖ • axis a.2) := by rw [axis_scale]
      _ = 0 := by rw [real_inner_smul_right, perp_rotation_inner _ _ hna, mul_zero]
  have hi := congrArg (fun z => inner ℝ z a.2) hc
  simp only [inner_add_left, real_inner_smul_left, hx, hrx, mul_zero, add_zero,
    perp_inner_self _ _ hnb] at hi
  have hbound := rotation_perp_bound A b hnb a.2
  have hmul := mul_le_mul_of_nonneg_left hbound
    (Real.sqrt_nonneg (b.1^2 - ‖b.2‖^2))
  have hlt := sqrt_lt_scalar b hb hnb
  -- Strict positivity of the coefficient gap forces the perpendicular part to vanish.
  -- Only nonnegativity of the square-root factor is used, so zero is included.
  have hy : perp b.2 a.2 = 0 := by
    have hn : ‖perp b.2 a.2‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖perp b.2 a.2‖]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (perp b.2 a.2)])
  refine ⟨inner ℝ (axis b.2) a.2 * ‖b.2‖⁻¹, ?_⟩
  simpa only [perp, sub_eq_zero, axis, smul_smul] using hy

/-- The equality case of Cauchy--Schwarz forced by the product equation.
The perpendicular-component argument above includes singular effects. -/
lemma compatible_inner_eq (A : AxisField d) (a b : Spin d)
    (hb : spinEffect b) (hna : a.2 ≠ 0) (hnb : b.2 ≠ 0)
    (h : spinProduct A a b = spinProduct A b a) :
    |inner ℝ a.2 b.2| = ‖a.2‖ * ‖b.2‖ := by
  obtain ⟨r, hr⟩ := compatible_implies_collinear A a b hb hna hnb h
  rw [hr, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖b.2‖)]
  ring

lemma collinear_implies_compatible (A : AxisField d) (a b : Spin d)
    (hna : a.2 ≠ 0) (hnb : b.2 ≠ 0) (h : ∃ r : ℝ, a.2 = r • b.2) :
    spinProduct A a b = spinProduct A b a := by
  obtain ⟨r, hr⟩ := h
  -- Inverting an arbitrary nonzero real covers both orientations of the axes.
  have hr0 : r ≠ 0 := by intro hz; apply hna; simp [hr, hz]
  have hy : perp b.2 a.2 = 0 := by rw [hr, perp_smul, perp_same, smul_zero]
  have hx : perp a.2 b.2 = 0 := by
    have hrev : b.2 = r⁻¹ • a.2 := by rw [hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [hrev, perp_smul, perp_same, smul_zero]
  apply Prod.ext
  · simp [spinProduct, hna, hnb, real_inner_comm, mul_comm]
  · rw [product_snd A a b hna, product_snd A b a hnb, hx, hy]
    simp [add_comm]

end SpinCompatibility
end PaperA

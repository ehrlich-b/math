import PaperA.Assembly
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

noncomputable section
open scoped BigOperators
namespace PaperA.QubitField

/-- The standard oriented cross product, transported to Euclidean space. -/
def cross (v w : Vec 3) : Vec 3 := WithLp.toLp 2 (crossProduct v w)

/-- Coordinate axes in the fixed orientation. -/
def e (i : Fin 3) : Vec 3 := EuclideanSpace.basisFun (Fin 3) ℝ i

/-- The axial vector of a skew operator, extracted without choosing a test vector. -/
def omega (A : AxisField 3) (v : Vec 3) : Vec 3 :=
  WithLp.toLp 2 ![(A.A v (e 1)) 2, (A.A v (e 2)) 0, (A.A v (e 0)) 1]

/-- The scalar coefficient along the unit axis. -/
def scalar (A : AxisField 3) (v : Vec 3) : ℝ :=
  v 0 * (A.A v (e 1)) 2 + v 1 * (A.A v (e 2)) 0 + v 2 * (A.A v (e 0)) 1

lemma norm_coordinates (v : Vec 3) (hv : ‖v‖ = 1) :
    v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq v
  rw [hv] at h
  simpa [Fin.sum_univ_succ, add_assoc] using h.symm

lemma skew_cross (A : AxisField 3) (v : Vec 3) (hv : ‖v‖ = 1) (w : Vec 3) :
    A.A v w = cross (omega A v) w := by
  have hs (i j : Fin 3) : (A.A v (e j)) i = -(A.A v (e i)) j := by
    simpa only [e, EuclideanSpace.basisFun_inner, EuclideanSpace.inner_basisFun_real] using
      A.skew v hv (e i) (e j)
  have hd (i : Fin 3) : (A.A v (e i)) i = 0 := by linarith [hs i i]
  have hw : w = ∑ i : Fin 3, w i • e i :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w |>.symm
  conv_lhs => rw [hw, map_sum]
  ext i
  fin_cases i <;>
    simp [cross, omega, cross_apply, Fin.sum_univ_succ, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul] <;>
    simp only [hd, hs 0 1, hs 0 2, hs 1 2]
    <;> ring

lemma omega_axis (A : AxisField 3) (v : Vec 3) (hv : ‖v‖ = 1) :
    omega A v = scalar A v • v := by
  have hf : crossProduct (omega A v) v = 0 := by
    have h := (skew_cross A v hv v).symm.trans (A.fixes v hv)
    exact congrArg WithLp.ofLp h
  have h := cross_cross_eq_smul_sub_smul (WithLp.ofLp (omega A v))
    (WithLp.ofLp v) (WithLp.ofLp v)
  have hn : dotProduct (WithLp.ofLp v) (WithLp.ofLp v) = 1 := by
    simpa [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc] using norm_coordinates v hv
  have hc : dotProduct (WithLp.ofLp (omega A v)) (WithLp.ofLp v) = scalar A v := by
    simp [omega, scalar, dotProduct, Fin.sum_univ_succ]
    ring
  rw [hf, map_zero, LinearMap.zero_apply, hn, hc, one_smul] at h
  exact WithLp.ofLp_injective 2 ((sub_eq_zero.mp h.symm).symm)

lemma axis_formula (A : AxisField 3) (v : Vec 3) (hv : ‖v‖ = 1) (w : Vec 3) :
    A.A v w = scalar A v • cross v w := by
  rw [skew_cross A v hv w, omega_axis A v hv]
  simp [cross]

lemma scalar_continuous (A : AxisField 3) :
    Continuous (fun v : sphere 3 => scalar A v.val) := by
  have hA : Continuous (fun v : sphere 3 => A.A v.val) :=
    continuousOn_iff_continuous_domRestrict.mp A.continuous
  have hcoord (i : Fin 3) : Continuous (fun v : sphere 3 => v.val i) :=
    (EuclideanSpace.proj i).continuous.comp continuous_subtype_val
  have hop (i j : Fin 3) : Continuous (fun v : sphere 3 => (A.A v.val (e i)) j) :=
    (EuclideanSpace.proj j).continuous.comp (hA.clm_apply continuous_const)
  exact ((hcoord 0 |>.mul (hop 1 2)).add (hcoord 1 |>.mul (hop 2 0))).add
    (hcoord 2 |>.mul (hop 0 1))

lemma scalar_even (A : AxisField 3) (v : Vec 3) (hv : ‖v‖ = 1) :
    scalar A (-v) = scalar A v := by
  simp [scalar, A.odd v hv]

/-- The continuous scalar descends through the antipodal quotient. -/
def frame (A : AxisField 3) : C(RP2, ℝ) :=
  ⟨Quotient.lift (fun v : sphere 3 => -scalar A v.val) (by
    intro v w h
    rcases h with h | h
    · simp [h]
    · simp [h, scalar_even A w.val w.property]), by
    apply continuous_coinduced_dom.mpr
    exact (scalar_continuous A).neg⟩

lemma frame_spec (A : AxisField 3) : FrameFunctionSpec (frame A) A := by
  intro v w
  simpa [frame, rp2Class, cross] using axis_formula A v.val v.property w

lemma scalar_of_spec (A : AxisField 3) (t : C(RP2, ℝ)) (ht : FrameFunctionSpec t A)
    (v : sphere 3) : scalar A v.val = -t (rp2Class v) := by
  have h0 := ht v (e 0)
  have h1 := ht v (e 1)
  have h2 := ht v (e 2)
  have h12 := congrArg (fun w : Vec 3 => w 2) h1
  have h20 := congrArg (fun w : Vec 3 => w 0) h2
  have h01 := congrArg (fun w : Vec 3 => w 1) h0
  simp [e, EuclideanSpace.basisFun_apply, cross_apply, PiLp.smul_apply,
    smul_eq_mul] at h12 h20 h01
  simp only [scalar, e, EuclideanSpace.basisFun_apply]
  rw [h12, h20, h01]
  calc
    _ = -t (rp2Class v) * (v.val 0 ^ 2 + v.val 1 ^ 2 + v.val 2 ^ 2) := by ring
    _ = -t (rp2Class v) := by rw [norm_coordinates v.val v.property, mul_one]

lemma frame_unique (A : AxisField 3) (t : C(RP2, ℝ)) (ht : FrameFunctionSpec t A) :
    t = frame A := by
  ext x
  induction x using Quotient.inductionOn with
  | h v =>
    change t (rp2Class v) = -scalar A v.val
    linarith [scalar_of_spec A t ht v]

lemma classification (A : AxisField 3) : ∃! t : C(RP2, ℝ), FrameFunctionSpec t A :=
  ⟨frame A, frame_spec A, fun t ht => frame_unique A t ht⟩

lemma constructor_spec (t : C(RP2, ℝ)) : FrameFunctionSpec t (fieldOfFrameFunction t) := by
  intro v w
  simp [fieldOfFrameFunction, v.property]


/-- Reflection in a unit axis is an orientation-preserving half turn in dimension three. -/
lemma half_turn_det (n : Vec 3) (hn : ‖n‖ = 1) :
    LinearMap.det (Submodule.reflection (ℝ ∙ n)).toLinearEquiv.toLinearMap = 1 := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have ho (x : Vec 3) : Submodule.reflection (ℝ ∙ n) x =
      (2 * inner ℝ n x) • n - x := by
    simp [Submodule.reflection_singleton_apply, hn, two_smul, two_mul, add_smul]
  have hm (i j : Fin 3) :
      LinearMap.toMatrix b b (Submodule.reflection (ℝ ∙ n)).toLinearEquiv.toLinearMap i j =
        2 * n j * n i - (if i = j then 1 else 0) := by
    simp [LinearMap.toMatrix_apply, b, ho, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_right, smul_eq_mul]
  rw [← LinearMap.det_toMatrix b]
  calc
    _ = 2 * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) - 1 := by
      rw [Matrix.det_fin_three]
      simp only [hm, Fin.reduceEq, ite_true, ite_false]
      ring
    _ = 1 := by rw [norm_coordinates n hn]; norm_num

/-- Half turns act transitively on unit axes, apart from the already identified antipodes. -/
lemma axes_transitive (v w : sphere 3) :
    rp2Class v = rp2Class w ∨
      ∃ O : Vec 3 ≃ₗᵢ[ℝ] Vec 3, LinearMap.det O.toLinearEquiv.toLinearMap = 1 ∧
        O v.val = w.val := by
  by_cases hz : v.val + w.val = 0
  · left
    exact Quotient.sound (Or.inr (eq_neg_of_add_eq_zero_left hz))
  · right
    let n : Vec 3 := ‖v.val + w.val‖⁻¹ • (v.val + w.val)
    have hn : ‖n‖ = 1 := norm_smul_inv_norm hz
    have hn0 : ‖v.val + w.val‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hz)
    have hspan : (ℝ ∙ n) = ℝ ∙ (v.val + w.val) := by
      exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hn0) _
    refine ⟨Submodule.reflection (ℝ ∙ n), half_turn_det n hn, ?_⟩
    have h := Submodule.reflection_sub (v := v.val) (w := -w.val)
      (by simp [v.property, w.property])
    simp only [sub_neg_eq_add, Submodule.reflection_orthogonal_apply] at h
    simpa only [hspan] using neg_injective h

lemma invariant_constant (t : C(RP2, ℝ))
    (h : ∀ O : Vec 3 ≃ₗᵢ[ℝ] Vec 3, LinearMap.det O.toLinearEquiv.toLinearMap = 1 →
      ∀ v : sphere 3, t (rp2Class ⟨O v.val, by simpa using v.property⟩) = t (rp2Class v)) :
    ∃ c : ℝ, ∀ x, t x = c := by
  let v : sphere 3 := ⟨e 0, by simp [e, EuclideanSpace.basisFun_apply]⟩
  refine ⟨t (rp2Class v), ?_⟩
  intro x
  induction x using Quotient.inductionOn with
  | h w =>
    rcases axes_transitive v w with he | ⟨O, hd, ho⟩
    · exact congrArg t he.symm
    · have ht := h O hd v
      change t (rp2Class w) = t (rp2Class v)
      simpa only [show (⟨O v.val, by simpa using v.property⟩ : sphere 3) = w from
        Subtype.ext ho] using ht

end PaperA.QubitField

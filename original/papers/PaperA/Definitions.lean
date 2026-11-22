import PaperA.FrameRefinement
import EuclideanJordan.Class
import EuclideanJordan.Rank
import EuclideanJordan.FrameExists
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.CrossProduct

/-! Paper A v2 statement blueprint. `sorry` is intentional proof debt.
No declaration in this package is a certified Paper A endpoint.
The EJA class is imported from the frozen local library, not assumed anew. -/
noncomputable section
open scoped BigOperators
open EuclideanJordan
namespace PaperA

variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J]

def Positive (a : J) : Prop := ∃ x : J, x * x = a
def Below (a b : J) : Prop := Positive (b - a)
def IsEffect (a : J) : Prop := Positive a ∧ Below a 1
def Effects (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] := {a : J // IsEffect a}
def StrictPositive (a : J) : Prop := ∃ ε : ℝ, 0 < ε ∧ Below (ε • (1 : J)) a
def ouNorm (a : J) : ℝ := sInf {r : ℝ | 0 ≤ r ∧ Below (-r • (1 : J)) a ∧ Below a (r • (1 : J))}
def Idempotent (p : J) : Prop := p * p = p
def Primitive (p : J) : Prop := p ≠ 0 ∧ Idempotent p ∧
  ∀ q : J, Idempotent q → Below 0 q → Below q p → q = 0 ∨ q = p
def Ideal (S : Submodule ℝ J) : Prop := ∀ x : J, ∀ y ∈ S, x * y ∈ S
def Simple (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] : Prop := Nontrivial J ∧
  ∀ S : Submodule ℝ J, Ideal S → S = ⊥ ∨ S = ⊤
def Q (x y : J) : J := (2 : ℝ) • (x * (x * y)) - (x * x) * y
def Peirce (p : J) (k : ℝ) : Set J := {x | p * x = k • x}
def Block {n : ℕ} (F : JordanFrame J n) (i j : Fin n) : Set J :=
  {x | F.p i * x = (1/2 : ℝ) • x ∧ F.p j * x = (1/2 : ℝ) • x}
structure COS (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] (n : ℕ) where
  p : Fin n → J
  nonzero : ∀ i, p i ≠ 0
  idem : ∀ i, Idempotent (p i)
  orth : ∀ i j, i ≠ j → p i * p j = 0
  complete : ∑ i, p i = 1
def Diagonal {n : ℕ} (p : Fin n → J) (a : J) : Prop :=
  ∃ lam : Fin n → ℝ, a = ∑ i, lam i • p i
structure Resolution (a : J) where
  n : ℕ
  frame : JordanFrame J n
  eigenvalue : Fin n → ℝ
  equation : a = ∑ i, eigenvalue i • frame.p i
def resolve (a : J) : Resolution a := by
  classical
  have h : Nonempty (Resolution a) := by
    obtain ⟨n, F, lam, h⟩ := primitive_spectral_frame a
    exact ⟨⟨n, F, lam, h⟩⟩
  exact Classical.choice h
def cfc (f : ℝ → ℝ) (a : J) : J :=
  ∑ i, f ((resolve a).eigenvalue i) • (resolve a).frame.p i
def sqrt (a : J) : J := cfc Real.sqrt a
def inverseSqrt (a : J) : J := cfc (fun x => (Real.sqrt x)⁻¹) a
def log (a : J) : J := cfc Real.log a
def jordanTrace (a : J) : ℝ := ∑ i, (resolve a).eigenvalue i
def support (a : J) : J := cfc (fun x => if 0 < x then 1 else 0) a
def luders (a b : J) : J := Q (sqrt a) b
def Compatible (sp : J → J → J) (a b : J) : Prop := sp a b = sp b a

/-- Total encoding, all operational clauses effect-guarded. Equality below is only on effects.
S2 explicitly uses the order-unit norm, without an arbitrary-topology field. -/
structure SequentialProduct (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] where
  sp : J → J → J
  closed : ∀ a b, IsEffect a → IsEffect b → IsEffect (sp a b)
  S1 : ∀ a b c, IsEffect a → IsEffect b → IsEffect c → IsEffect (b+c) →
    sp a (b+c) = sp a b + sp a c
  S2 : ∀ b, IsEffect b → ∀ a, IsEffect a → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ a', IsEffect a' → ouNorm (a'-a) < δ → ouNorm (sp a' b-sp a b) < ε
  S3 : ∀ a, IsEffect a → sp 1 a = a
  S4 : ∀ a b, IsEffect a → IsEffect b → sp a b = 0 → sp b a = 0
  S5 : ∀ a b c, IsEffect a → IsEffect b → IsEffect c → Compatible sp a b →
    sp a (sp b c) = sp (sp a b) c
  S6_compl : ∀ a b, IsEffect a → IsEffect b → Compatible sp a b → Compatible sp a (1-b)
  S6_sum : ∀ a b c, IsEffect a → IsEffect b → IsEffect c → IsEffect (b+c) →
    Compatible sp a b → Compatible sp a c → Compatible sp a (b+c)
  S7 : ∀ a b c, IsEffect a → IsEffect b → IsEffect c →
    Compatible sp a b → Compatible sp a c → Compatible sp a (sp b c)
def Agrees (sp tq : J → J → J) : Prop := ∀ a b, IsEffect a → IsEffect b → sp a b = tq a b
private abbrev jordanOrder (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : OrderUnitSpace J :=
  orderUnitSpaceOfBilinear (jmulₗ J) jmulₗ_comm jmulₗ_jordan jmulₗ_formallyReal
    1 jmulₗ_one_mul

section Ordered
attribute [local instance] jordanOrder

private theorem order_nonneg_iff (x : J) : 0 ≤ x ↔ Positive x := by
  change IsSoS (jmulₗ J) (x - 0) ↔ Positive x
  rw [sub_zero, isSoS_iff_exists_sq jmulₗ_comm jmulₗ_jordan jmulₗ_formallyReal
    jmulₗ_inner_assoc (1 : J) jmulₗ_one_mul]
  exact exists_congr fun _ => eq_comm

private theorem order_effect_iff (x : J) : OrderUnitSpace.IsEffect x ↔ IsEffect x := by
  change (0 ≤ x ∧ x ≤ (1 : J)) ↔ _
  rw [order_nonneg_iff, ← show (0 ≤ (1 : J) - x) ↔ x ≤ 1 from
    ⟨OrderUnitSpace.le_of_sub_nonneg, OrderUnitSpace.sub_nonneg_of_le⟩, order_nonneg_iff]
  rfl

/-- Positivity of the pairing of squares, from the Peirce operator estimate. -/
private theorem inner_nonneg_of_order_nonneg {x z : J} (hx : 0 ≤ x) (hz : 0 ≤ z) :
    0 ≤ inner ℝ x z := by
  obtain ⟨y, rfl⟩ := (order_nonneg_iff z).mp hz
  obtain ⟨n, p, l, hp, _, he⟩ := spectral_resolution_complete' x
  have hs : IsSoS (jmulₗ J) x := by
    change IsSoS (jmulₗ J) (x - 0) at hx
    simpa only [sub_zero] using hx
  rw [he, sum_inner]
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases hi : p i = 0
  · simp [hi]
  · rw [real_inner_smul_left]
    refine mul_nonneg (nonneg_coeff_of_isSoS jmulₗ_comm jmulₗ_jordan
      jmulₗ_inner_assoc hp.idem hp.orth he hs hi) ?_
    rw [← EuclideanJordanAlgebra.inner_assoc']
    exact inner_mul_self_nonneg_of_idem jmulₗ_comm jmulₗ_jordan jmulₗ_inner_assoc
      (hp.idem i) y

private theorem exists_pos_sub (x : J) : ∃ u v : J, 0 ≤ u ∧ 0 ≤ v ∧ x = u - v := by
  obtain ⟨r, hr, h⟩ := OrderUnitSpace.archimedean (-x)
  have hv := OrderUnitSpace.smul_nonneg' hr (OrderUnitSpace.ousUnit_nonneg (V := J))
  have hu := OrderUnitSpace.add_le_add_left _ _ h x
  rw [add_neg_cancel] at hu
  exact ⟨_, _, hu, hv, by abel⟩

private theorem positive_additive_real_linear (F : J →+ J)
    (hF : ∀ x, 0 ≤ x → 0 ≤ F x) (r : ℝ) (x : J) : F (r • x) = r • F x := by
  have ray (u : J) (hu : 0 ≤ u) : F (r • u) = r • F u := by
    have pairing (z : J) (hz : 0 ≤ z) : inner ℝ (F (r • u)) z =
        inner ℝ (r • F u) z := by
      let g : ℝ →+ ℝ :=
        { toFun := fun s => inner ℝ (F (s • u)) z
          map_zero' := by simp
          map_add' := fun s t => by simp [add_smul, inner_add_left] }
      have hg : Monotone g := by
        intro s t hst
        apply le_of_sub_nonneg
        change 0 ≤ inner ℝ (F (t • u)) z - inner ℝ (F (s • u)) z
        rw [← inner_sub_left, ← map_sub, ← sub_smul]
        exact inner_nonneg_of_order_nonneg
          (hF _ (OrderUnitSpace.smul_nonneg' (sub_nonneg.mpr hst) hu)) hz
      have hgcont : Continuous g := by
        apply g.continuous_of_isBounded_nhds_zero (Metric.ball_mem_nhds 0 zero_lt_one)
        apply Bornology.IsBounded.subset (isCompact_Icc (a := g (-1)) (b := g 1)).isBounded
        rintro _ ⟨s, hs, rfl⟩
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt] at hs
        exact ⟨hg hs.1.le, hg hs.2.le⟩
      have h := map_real_smul g hgcont r (1 : ℝ)
      simpa [g, smul_eq_mul, real_inner_smul_left] using h
    let w := F (r • u) - r • F u
    obtain ⟨v₁, v₂, hv₁, hv₂, hw⟩ := exists_pos_sub w
    have h₁ : inner ℝ w v₁ = 0 := by
      change inner ℝ (F (r • u) - r • F u) v₁ = 0
      rw [inner_sub_left, pairing v₁ hv₁, sub_self]
    have h₂ : inner ℝ w v₂ = 0 := by
      change inner ℝ (F (r • u) - r • F u) v₂ = 0
      rw [inner_sub_left, pairing v₂ hv₂, sub_self]
    have hzero : inner ℝ w w = 0 := by rw [hw, inner_sub_right, ← hw, h₁, h₂, sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_pos_sub x
  rw [smul_sub, map_sub, ray u hu, ray v hv, map_sub, smul_sub]

/-- Extend a positive, partially additive map on the effect interval by integer
rescaling on the cone and then by differences. -/
private theorem exists_left_extension (P : SequentialProduct J) (a : J) (ha : IsEffect a) :
    ∃ L : J →L[ℝ] J, (∀ b, IsEffect b → L b = P.sp a b) ∧
      ∀ x, Positive x → Positive (L x) := by
  classical
  let f := P.sp a
  let e : J := OrderUnitSpace.ousUnit
  let E : J → Prop := OrderUnitSpace.IsEffect
  have addEffect {u v : J} (hu : E u) (hv : E v) (hs : E (u + v)) :
      f (u + v) = f u + f v :=
    P.S1 a u v ha ((order_effect_iff u).mp hu) ((order_effect_iff v).mp hv)
      ((order_effect_iff _).mp hs)
  have fpos {x : J} (hx : E x) : 0 ≤ f x :=
    ((order_effect_iff _).mpr (P.closed a x ha ((order_effect_iff _).mp hx))).1
  have hz : E 0 := OrderUnitSpace.isEffect_zero
  have fzero : f 0 = 0 := by
    have h := addEffect hz hz (by simpa only [add_zero] using hz)
    rw [add_zero] at h
    exact add_left_cancel (show f 0 + f 0 = f 0 + 0 by simpa only [add_zero] using h.symm)
  have natEffect (n : ℕ) {x : J} (hx : 0 ≤ x) :
      E (n • x) → f (n • x) = n • f x := by
    induction n with
    | zero => intro _; simpa using fzero
    | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      intro h
      have hnp : 0 ≤ n • x := by
        rw [← Nat.cast_smul_eq_nsmul ℝ]
        exact OrderUnitSpace.smul_nonneg' (by positivity) hx
      have hn : E (n • x) :=
        ⟨hnp, (OrderUnitSpace.le_add_of_nonneg_right hx).trans h.2⟩
      have hxe : E x :=
        ⟨hx, (by
          apply le_trans (OrderUnitSpace.le_add_of_nonneg_right hnp)
          rw [add_comm]
          exact h.2)⟩
      rw [addEffect hn hxe h, ih hn]
  have scale {x : J} (hx : 0 ≤ x) : ∃ n : ℕ, 0 < n ∧ E ((n : ℝ)⁻¹ • x) := by
    obtain ⟨r, hr, hb⟩ := OrderUnitSpace.archimedean x
    obtain ⟨n, hn⟩ := exists_nat_gt r
    have hnp : 0 < (n : ℝ) := hr.trans_lt hn
    have hne : (n : ℝ) ≠ 0 := hnp.ne'
    have hle : x ≤ (n : ℝ) • e := hb.trans
      (OrderUnitSpace.smul_le_smul_of_le_of_nonneg hn.le OrderUnitSpace.ousUnit_nonneg)
    refine ⟨n, by exact_mod_cast hnp, OrderUnitSpace.smul_nonneg' (by positivity) hx, ?_⟩
    have h := OrderUnitSpace.smul_nonneg_mono ((n : ℝ)⁻¹) (by positivity) hle
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
  have common (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (x : J) :
      m • (((n : ℝ) * m)⁻¹ • x) = (n : ℝ)⁻¹ • x := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp [show (n : ℝ) ≠ 0 by positivity, show (m : ℝ) ≠ 0 by positivity]
  have independent {x : J} (hx : 0 ≤ x) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
      (hne : E ((n : ℝ)⁻¹ • x)) (hme : E ((m : ℝ)⁻¹ • x)) :
      n • f ((n : ℝ)⁻¹ • x) = m • f ((m : ℝ)⁻¹ • x) := by
    let y := ((n : ℝ) * m)⁻¹ • x
    have hy : 0 ≤ y := OrderUnitSpace.smul_nonneg' (by change 0 ≤ ((n : ℝ) * m)⁻¹; positivity) hx
    have h₁ : m • y = (n : ℝ)⁻¹ • x := common n m hn hm x
    have h₂ : n • y = (m : ℝ)⁻¹ • x := by
      simpa only [mul_comm (m : ℝ) (n : ℝ)] using common m n hm hn x
    have hme' : E (m • y) := h₁ ▸ hne
    have hne' : E (n • y) := h₂ ▸ hme
    rw [← h₁, ← h₂, natEffect m hy hme', natEffect n hy hne',
      smul_smul, smul_smul, Nat.mul_comm]
  let g : (x : J) → 0 ≤ x → J := fun x hx => (scale hx).choose •
    f (((scale hx).choose : ℝ)⁻¹ • x)
  have g_eq {x : J} (hx : 0 ≤ x) (n : ℕ) (hn : 0 < n)
      (he : E ((n : ℝ)⁻¹ • x)) : g x hx = n • f ((n : ℝ)⁻¹ • x) :=
    independent hx (scale hx).choose_spec.1 hn (scale hx).choose_spec.2 he
  have gpos {x : J} (hx : 0 ≤ x) : 0 ≤ g x hx := by
    dsimp [g]
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    exact OrderUnitSpace.smul_nonneg' (by positivity) (fpos (scale hx).choose_spec.2)
  have g_add {x y : J} (hx : 0 ≤ x) (hy : 0 ≤ y) :
      g (x + y) (OrderUnitSpace.add_nonneg hx hy) = g x hx + g y hy := by
    obtain ⟨n, hn, he⟩ := scale (OrderUnitSpace.add_nonneg hx hy)
    let c : ℝ := (n : ℝ)⁻¹
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hcx : 0 ≤ c • x := OrderUnitSpace.smul_nonneg' hc hx
    have hcy : 0 ≤ c • y := OrderUnitSpace.smul_nonneg' hc hy
    have he' : E (c • x + c • y) := by rwa [← smul_add]
    have hex : E (c • x) := ⟨hcx, (OrderUnitSpace.le_add_of_nonneg_right hcy).trans he'.2⟩
    have hey : E (c • y) := ⟨hcy, (by
      apply le_trans (OrderUnitSpace.le_add_of_nonneg_right hcx)
      rw [add_comm]
      exact he'.2)⟩
    rw [g_eq (OrderUnitSpace.add_nonneg hx hy) n hn he, g_eq hx n hn hex, g_eq hy n hn hey, smul_add,
      addEffect hex hey he', nsmul_add]
  have gzero : g 0 le_rfl = 0 := by
    rw [g_eq le_rfl 1 Nat.zero_lt_one (by simpa using hz)]
    simp [fzero]
  let decomp (x : J) := exists_pos_sub x
  let F (x : J) := g (decomp x).choose (decomp x).choose_spec.choose_spec.1 -
    g (decomp x).choose_spec.choose (decomp x).choose_spec.choose_spec.2.1
  have rep {x u v : J} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : x = u - v) :
      F x = g u hu - g v hv := by
    dsimp only [F]
    have hu'' := (decomp x).choose_spec.choose_spec.1
    have hv'' := (decomp x).choose_spec.choose_spec.2.1
    have h' : x = (decomp x).choose - (decomp x).choose_spec.choose :=
      (decomp x).choose_spec.choose_spec.2.2
    have ht : (decomp x).choose + v = u + (decomp x).choose_spec.choose :=
      sub_eq_sub_iff_add_eq_add.mp (h'.symm.trans h)
    have heq : g ((decomp x).choose + v) (OrderUnitSpace.add_nonneg hu'' hv) =
        g (u + (decomp x).choose_spec.choose) (OrderUnitSpace.add_nonneg hu hv'') := by
      generalize_proofs
      congr 1
    rw [g_add hu'' hv, g_add hu hv''] at heq
    exact sub_eq_sub_iff_add_eq_add.mpr heq
  let T : J →+ J :=
    { toFun := F
      map_zero' := by rw [rep le_rfl le_rfl (sub_zero (0 : J)).symm, sub_self]
      map_add' := by
        intro x y
        obtain ⟨u, v, hu, hv, h⟩ := decomp x
        obtain ⟨s, t, hs, ht, k⟩ := decomp y
        change F (x + y) = F x + F y
        have hsum : x + y = (u + s) - (v + t) := by rw [h, k]; abel
        rw [rep hu hv h, rep hs ht k,
          rep (OrderUnitSpace.add_nonneg hu hs) (OrderUnitSpace.add_nonneg hv ht) hsum,
          g_add hu hs, g_add hv ht]
        abel }
  have T_pos {x : J} (hx : 0 ≤ x) : T x = g x hx := by
    change F x = _
    rw [rep hx le_rfl (sub_zero x).symm, gzero, sub_zero]
  let L : J →ₗ[ℝ] J :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := positive_additive_real_linear T fun x hx => by rw [T_pos hx]; exact gpos hx }
  refine ⟨L.toContinuousLinearMap, ?_, ?_⟩
  · intro b hb
    have hbe := (order_effect_iff b).mpr hb
    change T b = f b
    rw [T_pos hbe.1, g_eq hbe.1 1 Nat.zero_lt_one (by simpa using hbe)]
    simp
  · intro x hx
    apply (order_nonneg_iff _).mp
    have h := (order_nonneg_iff _).mpr hx
    change 0 ≤ T x
    rw [T_pos h]
    exact gpos h

end Ordered

/-- The positive linear extension of `b ↦ P.sp a b` from the effects
(`lem:homog` in the manuscript). Off the effect interval use the zero map. -/
def leftMap (P : SequentialProduct J) (a : J) : J →L[ℝ] J := by
  classical
  exact if ha : IsEffect a then (exists_left_extension P a ha).choose else 0

/-- The defining extension property, including uniqueness. -/
theorem leftMap_spec (P : SequentialProduct J) (a : J) (ha : IsEffect a) :
    (∀ b, IsEffect b → leftMap P a b = P.sp a b) ∧
    (∀ x, Positive x → Positive (leftMap P a x)) ∧
    ∀ L : J →L[ℝ] J, (∀ b, IsEffect b → L b = P.sp a b) → L = leftMap P a := by
  have h : leftMap P a = (exists_left_extension P a ha).choose := by simp [leftMap, ha]
  have hs := (exists_left_extension P a ha).choose_spec
  rw [h]
  refine ⟨hs.1, hs.2, ?_⟩
  intro L hL
  let := jordanOrder J
  have eq := OrderUnitSpace.linearMap_eq_of_eq_on_effects L.toLinearMap
    (exists_left_extension P a ha).choose.toLinearMap fun b hb =>
      (hL b ((order_effect_iff b).mp hb)).trans (hs.1 b ((order_effect_iff b).mp hb)).symm
  exact ContinuousLinearMap.ext (LinearMap.congr_fun eq)
def theta (P : SequentialProduct J) (a x : J) : J := Q (inverseSqrt a) (leftMap P a x)
def JordanAuto (g : J ≃ₗ[ℝ] J) : Prop := g 1 = 1 ∧ ∀ x y, g (x*y) = g x * g y
def Derivation (D : J →ₗ[ℝ] J) : Prop := ∀ x y, D (x*y) = D x*y + x*D y
def twistElt {n : ℕ} (F : JordanFrame J n) (r : Fin n → ℝ) : J :=
  ∑ i, Real.exp (r i) • F.p i

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Spin (d : ℕ) := ℝ × Vec d
def spinMul {d : ℕ} (a b : Spin d) : Spin d :=
  (a.1*b.1 + inner ℝ a.2 b.2, a.1 • b.2 + b.1 • a.2)
def spinUnit (d : ℕ) : Spin d := (1,0)
def spinAtom {d : ℕ} (v : Vec d) : Spin d := ((1/2 : ℝ), (1/2 : ℝ) • v)
def spinPositive {d : ℕ} (a : Spin d) : Prop := ‖a.2‖ ≤ a.1
def spinEffect {d : ℕ} (a : Spin d) : Prop := spinPositive a ∧ spinPositive (spinUnit d-a)
abbrev sphere (d : ℕ) := {v : Vec d // ‖v‖ = 1}
/-- Ambient continuous operator field restricted to the sphere, avoiding a choice of tangent basis. -/
structure AxisField (d : ℕ) where
  A : Vec d → (Vec d →L[ℝ] Vec d)
  continuous : ContinuousOn A {v | ‖v‖ = 1}
  skew : ∀ v, ‖v‖ = 1 → ∀ x y, inner ℝ x (A v y) = -inner ℝ (A v x) y
  fixes : ∀ v, ‖v‖ = 1 → A v v = 0
  odd : ∀ v, ‖v‖ = 1 → A (-v) = -A v
def FieldEq {d : ℕ} (A B : AxisField d) : Prop := ∀ v, ‖v‖ = 1 → A.A v = B.A v
def spinRotation {d : ℕ} (A : AxisField d) (a : Spin d) : Vec d →L[ℝ] Vec d :=
  if a.2 = 0 ∨ a.1 ≤ ‖a.2‖ then ContinuousLinearMap.id ℝ (Vec d)
  else NormedSpace.exp (Real.log ((a.1+‖a.2‖)/(a.1-‖a.2‖)) • A.A (‖a.2‖⁻¹ • a.2))
/-- Formula (7), with scalar and singular branches explicit. -/
def spinProduct {d : ℕ} (A : AxisField d) (a b : Spin d) : Spin d :=
  if a.2 = 0 then a.1 • b else
  let u := ‖a.2‖⁻¹ • a.2
  let z := inner ℝ u b.2
  (a.1*b.1 + inner ℝ a.2 b.2,
   b.1 • a.2 + (a.1*z) • u + Real.sqrt (a.1^2-‖a.2‖^2) • spinRotation A a (b.2-z • u))
structure SpinModel (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] (d : ℕ) where
  equiv : J ≃ₗ[ℝ] Spin d
  unit : equiv 1 = spinUnit d
  mul : ∀ x y, equiv (x*y) = spinMul (equiv x) (equiv y)
def spinOn {d : ℕ} (M : SpinModel J d) (A : AxisField d) (a b : J) : J :=
  M.equiv.symm (spinProduct A (M.equiv a) (M.equiv b))

/-- Concrete positive-definite Cayley--Dickson carrier, not Tau Ceti's split carrier. -/
abbrev Oct := Quaternion ℝ × Quaternion ℝ
def octConj (x : Oct) : Oct := (star x.1, -x.2)
def octMul (x y : Oct) : Oct := (x.1*y.1 - star y.2*x.2, y.2*x.1 + x.2*star y.1)
def octOne : Oct := (1,0)
def rawMatMul {K : Type} [AddCommMonoid K] (mul : K → K → K) {n : ℕ}
    (a b : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := fun i j => ∑ k, mul (a i k) (b k j)
structure MatrixModel (J K : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [AddCommGroup K] [Module ℝ K]
    (mul : K → K → K) (conj : K → K) (one : K) (n : ℕ) where
  map : J →ₗ[ℝ] Matrix (Fin n) (Fin n) K
  injective : Function.Injective map
  range : ∀ a, (∃ x, map x = a) ↔ ∀ i j, conj (a j i) = a i j
  unit : ∀ i j, map 1 i j = if i = j then one else 0
  product : ∀ x y, map (x*y) = (1/2 : ℝ) •
    (rawMatMul mul (map x) (map y) + rawMatMul mul (map y) (map x))
abbrev RealModel (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J] (n : ℕ) :=
  MatrixModel J ℝ (·*·) id 1 n
abbrev ComplexModel (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J] (n : ℕ) :=
  MatrixModel J ℂ (·*·) star 1 n
abbrev QuaternionModel (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J] (n : ℕ) :=
  MatrixModel J (Quaternion ℝ) (·*·) star 1 n
abbrev AlbertModel (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J] :=
  MatrixModel J Oct octMul octConj octOne 3
def twistFactor {n : ℕ} (M : ComplexModel J n) (t : ℝ) (a : J) : Matrix (Fin n) (Fin n) ℂ :=
  M.map (cfc (fun x => Real.sqrt x * Real.cos (t*Real.log x)) a) +
  Complex.I • M.map (cfc (fun x => Real.sqrt x * Real.sin (t*Real.log x)) a)
def phaseUnit {n : ℕ} (M : ComplexModel J n) (t : ℝ) (a : J) : Matrix (Fin n) (Fin n) ℂ :=
  M.map (1-support a) + M.map (cfc (fun x => if 0 < x then Real.cos (t*Real.log x) else 0) a) +
    Complex.I • M.map (cfc (fun x => if 0 < x then Real.sin (t*Real.log x) else 0) a)
def adjointAction {n : ℕ} (u x : Matrix (Fin n) (Fin n) ℂ) := u*x*u.conjTranspose
def Twist {n : ℕ} (M : ComplexModel J n) (t : ℝ) (sp : J → J → J) : Prop :=
  ∀ a b, IsEffect a → IsEffect b → M.map (sp a b) =
    twistFactor M t a * M.map b * (twistFactor M t a).conjTranspose
def Rigid (P : SequentialProduct J) : Prop := Agrees P.sp luders
def HasComplexModel (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] : Prop := ∃ n : ℕ, 0 < n ∧ Nonempty (ComplexModel J n)
structure DynamicalCorrespondence (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] where
  psi : J →ₗ[ℝ] (J →ₗ[ℝ] J)
  derivation : ∀ a, Derivation (psi a)
  fixes : ∀ a, psi a a = 0
  bracket : ∀ a b x, psi a (psi b x)-psi b (psi a x) = -(a*(b*x)-b*(a*x))

end PaperA

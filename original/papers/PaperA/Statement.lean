import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Sequential products on finite-dimensional Euclidean Jordan algebras

The definitions and the scalar witnesses in this file require only Mathlib.
The statement of Paper A is the conjunction at the end of the file.

Manuscript: B. Ehrlich, *Sequential Products on Euclidean Jordan Algebras: Classification in Rank at Least Three and the Complex Qubit* (submitted).
-/

noncomputable section
open scoped BigOperators
namespace PaperA.Statement

/-- The real unital commutative Jordan product and its associative inner product
(`sec:eja`). Finite dimensionality is supplied where used. -/
class EuclideanJordanAlgebra (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    extends Mul J, One J where
  mul_comm : ∀ x y : J, x * y = y * x
  add_mul : ∀ x y z : J, (x + y) * z = x * z + y * z
  smul_mul : ∀ (r : ℝ) (x y : J), (r • x) * y = r • (x * y)
  one_mul : ∀ x : J, (1 : J) * x = x
  jordan : ∀ x y : J, x * ((x * x) * y) = (x * x) * (x * y)
  inner_assoc : ∀ x y z : J, inner ℝ (x * y) z = inner ℝ y (x * z)

variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J]

private theorem mul_add (x y z : J) : x * (y + z) = x * y + x * z := by
  rw [EuclideanJordanAlgebra.mul_comm x (y + z), EuclideanJordanAlgebra.add_mul,
    EuclideanJordanAlgebra.mul_comm y x, EuclideanJordanAlgebra.mul_comm z x]

private theorem mul_smul (r : ℝ) (x y : J) : x * (r • y) = r • (x * y) := by
  rw [EuclideanJordanAlgebra.mul_comm x (r • y), EuclideanJordanAlgebra.smul_mul,
    EuclideanJordanAlgebra.mul_comm y x]

private theorem jordan_mul_zero (x : J) : x * 0 = 0 := by
  simpa only [zero_smul] using mul_smul 0 x (0 : J)

private theorem mul_sum {ι : Type*} (s : Finset ι) (x : J) (q : ι → J) :
    x * (∑ i ∈ s, q i) = ∑ i ∈ s, x * q i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jordan_mul_zero]
  | insert i s hi ih => simp only [Finset.sum_insert hi, mul_add, ih]

/-- The rank in `sec:eja`, computed as the largest size of an orthogonal
family of nonzero idempotents. -/
def rank (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] : ℕ :=
  sSup {n | ∃ p : Fin n → J, (∀ i, p i * p i = p i) ∧
    (∀ i j, i ≠ j → p i * p j = 0) ∧ (∀ i, p i ≠ 0)}

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

/-- A complete spectral decomposition of `a` (`sec:eja`). The idempotents
may be grouped by eigenvalue since the calculus sums their contributions. -/
structure Resolution (a : J) where
  n : ℕ
  p : Fin n → J
  idem : ∀ i, p i * p i = p i
  orth : ∀ i j, i ≠ j → p i * p j = 0
  complete : ∑ i, p i = 1
  eigenvalue : Fin n → ℝ
  equation : a = ∑ i, eigenvalue i • p i

def Resolution.eval {a : J} (R : Resolution a) (f : ℝ → ℝ) : J :=
  ∑ i, f (R.eigenvalue i) • R.p i

private theorem Resolution.mul_eval {a : J} (R : Resolution a) (f : ℝ → ℝ)
    (i : Fin R.n) : R.p i * R.eval f = f (R.eigenvalue i) • R.p i := by
  classical
  rw [Resolution.eval, mul_sum, Finset.sum_eq_single i]
  · rw [mul_smul, R.idem]
  · intro j _ hji
    rw [mul_smul, R.orth _ _ hji.symm, smul_zero]
  · simp

private theorem Resolution.eigen {a : J} (R : Resolution a) (i : Fin R.n) :
    a * R.p i = R.eigenvalue i • R.p i := by
  calc
    a * R.p i = R.p i * a := EuclideanJordanAlgebra.mul_comm _ _
    _ = R.p i * R.eval id := congrArg (fun x => R.p i * x) R.equation
    _ = _ := R.mul_eval id i

private theorem Resolution.inner_eval {a : J} (R S : Resolution a) (f : ℝ → ℝ)
    (j : Fin S.n) : inner ℝ (R.eval f) (S.p j) =
      f (S.eigenvalue j) * inner ℝ (1 : J) (S.p j) := by
  rw [Resolution.eval, ← R.complete]
  simp only [sum_inner, real_inner_smul_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : R.eigenvalue i = S.eigenvalue j
  · rw [h]
  · have he := EuclideanJordanAlgebra.inner_assoc a (R.p i) (S.p j)
    rw [R.eigen, S.eigen, real_inner_smul_left, real_inner_smul_right] at he
    have hz : inner ℝ (R.p i) (S.p j) = 0 :=
      (mul_eq_zero.mp (show (R.eigenvalue i - S.eigenvalue j) *
        inner ℝ (R.p i) (S.p j) = 0 by rw [sub_mul, he, sub_self])).resolve_left
        (sub_ne_zero.mpr h)
    simp only [hz, mul_zero]

theorem Resolution.eval_eq {a : J} (R S : Resolution a) (f : ℝ → ℝ) :
    R.eval f = S.eval f := by
  let w := R.eval f - S.eval f
  have h (T : Resolution a) (j : Fin T.n) : inner ℝ w (T.p j) = 0 := by
    change inner ℝ (R.eval f - S.eval f) (T.p j) = 0
    rw [inner_sub_left, R.inner_eval T, S.inner_eval T, sub_self]
  have he (T : Resolution a) : inner ℝ w (T.eval f) = 0 := by
    simp [Resolution.eval, inner_sum, real_inner_smul_right, h T]
  apply sub_eq_zero.mp
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (by
    change inner ℝ w (R.eval f - S.eval f) = 0
    rw [inner_sub_right, he R, he S, sub_self])

/-- Apply a scalar function to the eigenvalues (`sec:eja`). The total
fallback is used only when no resolution is supplied by the spectral theorem. -/
def cfc (f : ℝ → ℝ) (a : J) : J := by
  classical
  exact if h : Nonempty (Resolution a) then (Classical.choice h).eval f else 0

theorem cfc_eq {a : J} (R : Resolution a) (f : ℝ → ℝ) : cfc f a = R.eval f := by
  have h : Nonempty (Resolution a) := ⟨R⟩
  rw [cfc, dif_pos h]
  exact (Classical.choice h).eval_eq R f

def sqrt (a : J) : J := cfc Real.sqrt a
def inverseSqrt (a : J) : J := cfc (fun x => (Real.sqrt x)⁻¹) a
def log (a : J) : J := cfc Real.log a
def support (a : J) : J := cfc (fun x => if 0 < x then 1 else 0) a
def luders (a b : J) : J := Q (sqrt a) b
def Compatible (sp : J → J → J) (a b : J) : Prop := sp a b = sp b a

variable [FiniteDimensional ℝ J]

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

/-- The positive linear extension of `b ↦ P.sp a b` from the effect interval
(`lem:homog`). The total fallback is zero. -/
def leftMap (P : SequentialProduct J) (a : J) : J →L[ℝ] J := by
  classical
  exact if IsEffect a then
    if h : ∃ L : J →L[ℝ] J, (∀ b, IsEffect b → L b = P.sp a b) ∧
        (∀ x, Positive x → Positive (L x)) then h.choose else 0
  else 0

def theta (P : SequentialProduct J) (a x : J) : J :=
  Q (inverseSqrt a) (leftMap P a x)

def Derivation (D : J →ₗ[ℝ] J) : Prop := ∀ x y, D (x*y) = D x*y + x*D y
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Spin (d : ℕ) := ℝ × Vec d
def spinMul {d : ℕ} (a b : Spin d) : Spin d :=
  (a.1*b.1 + inner ℝ a.2 b.2, a.1 • b.2 + b.1 • a.2)
def spinUnit (d : ℕ) : Spin d := (1,0)
def spinAtom {d : ℕ} (v : Vec d) : Spin d := ((1/2 : ℝ), (1/2 : ℝ) • v)
def spinPositive {d : ℕ} (a : Spin d) : Prop := ‖a.2‖ ≤ a.1
def spinEffect {d : ℕ} (a : Spin d) : Prop := spinPositive a ∧ spinPositive (spinUnit d-a)
abbrev sphere (d : ℕ) := {v : Vec d // ‖v‖ = 1}
/-- An operator field with continuity and the axis laws imposed on the sphere. -/
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

/-- The positive-definite Cayley–Dickson carrier over the real quaternions. -/
abbrev Oct := Quaternion ℝ × Quaternion ℝ
def octConj (x : Oct) : Oct := (star x.1, -x.2)
def octMul (x y : Oct) : Oct := (x.1*y.1 - star y.2*x.2, y.2*x.1 + x.2*star y.1)
def octOne : Oct := (1,0)
def rawMatMul {K : Type} [AddCommMonoid K] (mul : K → K → K) {n : ℕ}
    (a b : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  fun i j => ∑ k, mul (a i k) (b k j)
structure MatrixModel (J K : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [AddCommGroup K] [Module ℝ K]
    (mul : K → K → K) (conj : K → K) (one : K) (n : ℕ) where
  map : J →ₗ[ℝ] Matrix (Fin n) (Fin n) K
  injective : Function.Injective map
  range : ∀ a, (∃ x, map x = a) ↔ ∀ i j, conj (a j i) = a i j
  unit : ∀ i j, map 1 i j = if i = j then one else 0
  product : ∀ x y, map (x*y) = (1/2 : ℝ) •
    (rawMatMul mul (map x) (map y) + rawMatMul mul (map y) (map x))
abbrev RealModel (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] (n : ℕ) :=
  MatrixModel J ℝ (·*·) id 1 n
abbrev ComplexModel (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] (n : ℕ) :=
  MatrixModel J ℂ (·*·) star 1 n
abbrev QuaternionModel (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] (n : ℕ) :=
  MatrixModel J (Quaternion ℝ) (·*·) star 1 n
abbrev AlbertModel (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] :=
  MatrixModel J Oct octMul octConj octOne 3
def twistFactor {n : ℕ} (M : ComplexModel J n) (t : ℝ) (a : J) : Matrix (Fin n) (Fin n) ℂ :=
  M.map (cfc (fun x => Real.sqrt x * Real.cos (t*Real.log x)) a) +
  Complex.I • M.map (cfc (fun x => Real.sqrt x * Real.sin (t*Real.log x)) a)
def phaseUnit {n : ℕ} (M : ComplexModel J n) (t : ℝ) (a : J) : Matrix (Fin n) (Fin n) ℂ :=
  M.map (1-support a) + M.map (cfc (fun x => if 0 < x then Real.cos (t*Real.log x) else 0) a) +
    Complex.I • M.map (cfc (fun x => if 0 < x then Real.sin (t*Real.log x) else 0) a)
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

structure Object where
  V : Type
  [normed : NormedAddCommGroup V]
  [inner : InnerProductSpace ℝ V]
  [jordan : EuclideanJordanAlgebra V]
  [finite : FiniteDimensional ℝ V]
attribute [instance] Object.normed Object.inner Object.jordan Object.finite

structure Decomposition (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] where
  n : ℕ
  blocks : Fin n → Object
  simple : ∀ i, Simple (blocks i).V
  equiv : J ≃ₗ[ℝ] (∀ i, (blocks i).V)
  unit : ∀ i, equiv 1 i = 1
  mul : ∀ x y i, equiv (x*y) i = equiv x i * equiv y i

def ProductSpace (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] :=
  { f : Effects J → Effects J → Effects J //
    ∃ P : SequentialProduct J, ∀ a b, (f a b).val = P.sp a.val b.val }

def FieldSetoid (d : ℕ) : Setoid (AxisField d) where
  r := FieldEq
  iseqv := ⟨fun _ _ _ => rfl, fun h v hv => (h v hv).symm,
    fun h₁ h₂ v hv => (h₁ v hv).trans (h₂ v hv)⟩
abbrev FieldSpace (d : ℕ) := Quotient (FieldSetoid d)

/-- The antipodal sphere quotient, with its quotient topology: a concrete RP² model. -/
def Antipodal : Setoid (sphere 3) where
  r v w := v.val = w.val ∨ v.val = -w.val
  iseqv := by
    constructor
    · intro v
      exact Or.inl rfl
    · intro v w h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        simpa using congrArg Neg.neg h.symm
    · intro u v w h₁ h₂
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact Or.inl (h₁.trans h₂)
      · exact Or.inr (h₁.trans h₂)
      · exact Or.inr (h₁.trans (congrArg Neg.neg h₂))
      · left
        simpa using h₁.trans (congrArg Neg.neg h₂)
abbrev RP2 := Quotient Antipodal
instance rp2Topology : TopologicalSpace RP2 :=
  TopologicalSpace.coinduced (Quotient.mk Antipodal) inferInstance
def rp2Class (v : sphere 3) : RP2 := Quotient.mk Antipodal v
def fieldOfFrameFunction (t : C(RP2, ℝ)) : AxisField 3 := by
  classical
  let crossB : Vec 3 →ₗ[ℝ] Vec 3 →ₗ[ℝ] Vec 3 :=
    LinearMap.mk₂ ℝ (fun v w => WithLp.toLp 2 (crossProduct (WithLp.ofLp v) (WithLp.ofLp w)))
      (by intro v u w; simp)
      (by intro r v w; simp)
      (by intro v w u; simp)
      (by intro r v w; simp)
  let crossL : Vec 3 →L[ℝ] Vec 3 →L[ℝ] Vec 3 :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp crossB)
  have hc (v w : Vec 3) : crossL v w = WithLp.toLp 2 (crossProduct v w) := rfl
  let F : Vec 3 → (Vec 3 →L[ℝ] Vec 3) := fun v =>
    if hv : ‖v‖ = 1 then -(t (rp2Class ⟨v, hv⟩)) • crossL v else 0
  have hF (v : sphere 3) : F v.val = -(t (rp2Class v)) • crossL v.val := by
    simp [F, v.property]
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have ht : Continuous (fun v : sphere 3 => t (rp2Class v)) :=
      t.continuous.comp continuous_coinduced_rng
    exact (ht.neg.smul (crossL.continuous.comp continuous_subtype_val)).congr
      (fun v => (hF v).symm)
  · intro v hv x y
    rw [hF ⟨v, hv⟩]
    simp only [smul_apply, real_inner_smul_right,
      real_inner_smul_left, hc]
    suffices inner ℝ x (WithLp.toLp 2 (crossProduct v y)) =
        -inner ℝ (WithLp.toLp 2 (crossProduct v x)) y by rw [this]; ring
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ,
      cross_apply]
    ring
  · intro v hv
    rw [hF ⟨v, hv⟩]
    simp [hc]
  · intro v hv
    have hn : ‖-v‖ = 1 := by simpa using hv
    have hp : rp2Class ⟨-v, hn⟩ = rp2Class ⟨v, hv⟩ :=
      Quotient.sound (Or.inr rfl)
    rw [hF ⟨-v, hn⟩, hF ⟨v, hv⟩, hp, map_neg]
    module
def FrameFunctionSpec (t : C(RP2, ℝ)) (A : AxisField 3) : Prop :=
  ∀ (v : sphere 3) (w : Vec 3), A.A v.val w =
    -(t (rp2Class v)) • (WithLp.toLp 2 (crossProduct v.val w))

/-- Model labels include all dimensional riders. -/
inductive Label where
  | scalar
  | real (n : ℕ) (hn : 2 ≤ n)
  | complex (n : ℕ) (hn : 3 ≤ n)
  | quaternion (n : ℕ) (hn : 3 ≤ n)
  | albert
  | spin (d : ℕ) (hd : 3 ≤ d)
def Label.Param : Label → Type
  | .complex _ _ => ℝ
  | .spin d _ => FieldSpace d
  | _ => Unit
def Realizes (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] : Label → Prop
  | .scalar => Nonempty (RealModel J 1)
  | .real n _ => Nonempty (RealModel J n)
  | .complex n _ => Nonempty (ComplexModel J n)
  | .quaternion n _ => Nonempty (QuaternionModel J n)
  | .albert => Nonempty (AlbertModel J)
  | .spin d _ => Nonempty (SpinModel J d)

def ModelWitness (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] : Label → Type
  | .scalar => RealModel J 1
  | .real n _ => RealModel J n
  | .complex n _ => ComplexModel J n
  | .quaternion n _ => QuaternionModel J n
  | .albert => AlbertModel J
  | .spin d _ => SpinModel J d
def ParamSpec (ℓ : Label) (W : ModelWitness J ℓ) (p : ℓ.Param)
    (f : ProductSpace J) : Prop :=
  match ℓ with
  | .complex _ _ => ∀ a b, W.map ((f.val a b).val) =
      twistFactor W p a.val * W.map b.val * (twistFactor W p a.val).conjTranspose
  | .spin d _ => ∃ A : AxisField d, Quotient.mk (FieldSetoid d) A = p ∧
      ∀ a b, (f.val a b).val = spinOn W A a.val b.val
  | _ => ∀ a b, (f.val a b).val = luders a.val b.val

/-- The projection of an effect to one summand, as in `prop:central`. -/
def componentEffect (D : Decomposition J) (a : Effects J) (i : Fin D.n) :
    Effects (D.blocks i).V := by
  refine ⟨D.equiv a.val i, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := a.property.1
    exact ⟨D.equiv x i, (D.mul x x i).symm.trans (congrArg (fun v => D.equiv v i) hx)⟩
  · obtain ⟨x, hx⟩ := a.property.2
    refine ⟨D.equiv x i, ?_⟩
    rw [← D.mul, hx]
    rw [map_sub, Pi.sub_apply, D.unit]

/-- Coordinatewise multiplication of effects in a direct sum
(`mthm:omnibus`, `prop:central`). -/
def Componentwise (D : Decomposition J) (P : ProductSpace J)
    (parts : ∀ i, ProductSpace (D.blocks i).V) : Prop :=
  ∀ a b i, D.equiv (P.val a b).val i =
    ((parts i).val (componentEffect D a i) (componentEffect D b i)).val



section Scalar

/-- The manuscript's rank-one example (`mthm:omnibus`), with the usual real product. -/
scoped instance realJordanAlgebra : EuclideanJordanAlgebra ℝ where
  toMul := inferInstance
  toOne := inferInstance
  mul_comm := _root_.mul_comm
  add_mul := _root_.add_mul
  smul_mul := by intros; simp only [smul_eq_mul, mul_assoc]
  one_mul := _root_.one_mul
  jordan := by intros; ring
  inner_assoc := by intros; simp only [Real.inner_apply]; ring

private theorem real_positive_iff (a : ℝ) : Positive a ↔ 0 ≤ a := by
  constructor
  · rintro ⟨x, rfl⟩
    exact mul_self_nonneg x
  · intro h
    exact ⟨Real.sqrt a, Real.mul_self_sqrt h⟩

private theorem real_effect_iff (a : ℝ) : IsEffect a ↔ a ∈ Set.Icc (0 : ℝ) 1 := by
  change (Positive a ∧ Positive (1 - a)) ↔ _
  rw [real_positive_iff, real_positive_iff, sub_nonneg]
  rfl

private theorem real_ouNorm (a : ℝ) : ouNorm a = |a| := by
  unfold ouNorm
  rw [show {r : ℝ | 0 ≤ r ∧ Below (-r • (1 : ℝ)) a ∧ Below a (r • (1 : ℝ))} =
      Set.Ici |a| by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, Below, smul_eq_mul, mul_one,
      real_positive_iff, sub_nonneg, abs_le]
    exact ⟨fun h => h.2, fun h => ⟨(abs_nonneg a).trans (abs_le.mpr h), h⟩⟩,
    csInf_Ici]

private theorem real_luders (a b : ℝ) (ha : 0 ≤ a) : luders a b = a * b := by
  let R : Resolution a :=
    { n := 1, p := fun _ => 1, idem := by simp, orth := by
        intro i j h
        exact (h (Subsingleton.elim i j)).elim
      complete := by simp
      eigenvalue := fun _ => a
      equation := by simp }
  have hs : sqrt a = Real.sqrt a := by
    rw [sqrt, cfc_eq R]
    simp [Resolution.eval, R, smul_eq_mul]
  have hsq := Real.mul_self_sqrt ha
  unfold luders Q
  rw [hs]
  simp only [smul_eq_mul]
  calc
    2 * (Real.sqrt a * (Real.sqrt a * b)) - Real.sqrt a * Real.sqrt a * b =
        (Real.sqrt a * Real.sqrt a) * b := by ring
    _ = a * b := by rw [hsq]

/-- Ordinary multiplication is a sequential product on the real effect interval. -/
def realLudersProduct : SequentialProduct ℝ where
  sp := (· * ·)
  closed := by
    intro a b ha hb
    rw [real_effect_iff] at ha hb ⊢
    exact ⟨mul_nonneg ha.1 hb.1, mul_le_one₀ ha.2 hb.1 hb.2⟩
  S1 := by intros; apply _root_.mul_add
  S2 := by
    intro b hb a _ ε hε
    refine ⟨ε, hε, ?_⟩
    intro a' _ h
    rw [real_ouNorm] at h
    change ouNorm (a' * b - a * b) < ε
    rw [real_ouNorm, ← sub_mul, abs_mul, abs_of_nonneg (real_effect_iff b |>.mp hb).1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (real_effect_iff b |>.mp hb).2).trans_lt h
  S3 := by intros; simp
  S4 := by intro a b _ _ h; simpa [_root_.mul_comm b a] using h
  S5 := by intros; apply (_root_.mul_assoc _ _ _).symm
  S6_compl := by intros; apply _root_.mul_comm
  S6_sum := by intros; apply _root_.mul_comm
  S7 := by intros; apply _root_.mul_comm

/-- The rank-one Lüders product satisfies closure and all seven axioms. -/
theorem luders_witness : ∃ P : SequentialProduct ℝ, Agrees P.sp luders :=
  ⟨realLudersProduct, fun a b ha _ => (real_luders a b (real_effect_iff a |>.mp ha).1).symm⟩

/-- The constant zero operation preserves effects but fails S3 at the unit. -/
theorem discrimination_witness :
    (∀ a b : ℝ, IsEffect a → IsEffect b → IsEffect ((fun _ _ : ℝ => (0 : ℝ)) a b)) ∧
      ∃ a : ℝ, IsEffect a ∧ (fun _ _ : ℝ => (0 : ℝ)) 1 a ≠ a := by
  refine ⟨fun _ _ _ _ => (real_effect_iff 0).mpr (by norm_num), 1,
    (real_effect_iff 1).mpr (by norm_num), zero_ne_one⟩

end Scalar

/-- `mthm:omnibus`, `prop:central` — every parameter tuple is realized
uniquely on the fixed labelled algebra, and the product acts coordinatewise. -/
def Omnibus (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ (D : Decomposition J) (ℓ : Fin D.n → Label)
    (M : ∀ i, ModelWitness (D.blocks i).V (ℓ i)),
    ∃ restrict : ProductSpace J ≃ (∀ i, ProductSpace (D.blocks i).V),
      (∀ P, Componentwise D P (restrict P)) ∧
      ∃ e : ProductSpace J ≃ (∀ i, (ℓ i).Param), ∀ P i,
        ParamSpec (ℓ i) (M i) (e P i) (restrict P i)

/-- `mthm:dyn` — on invertible effects the matrix correspondence produces
the displayed flow. The twisted formula specifies its extension to all effects. -/
def FlowFormula (P : SequentialProduct J) (ψ : DynamicalCorrespondence J) (t : ℝ) : Prop :=
  ∀ a b, IsEffect a → StrictPositive a → IsEffect b →
    P.sp a b = Q (sqrt a) (NormedSpace.exp ((2 * t) •
      (ψ.psi (log a)).toContinuousLinearMap) b)

/-- `mthm:dyn` — every sequential product has a unique flow parameter,
every parameter occurs, and the same formula extends to singular effects. -/
def DynamicalFlow (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ {n : ℕ} (M : ComplexModel J n), 3 ≤ n →
    ∃ ψ : DynamicalCorrespondence J,
      (∀ h x, M.map (ψ.psi h x) =
        (Complex.I / 2) • (M.map h * M.map x - M.map x * M.map h)) ∧
      (∀ P : SequentialProduct J, ∀ t : ℝ, FlowFormula P ψ t ↔ Twist M t P.sp) ∧
      (∀ P : SequentialProduct J, ∃! t : ℝ, FlowFormula P ψ t) ∧
      (∀ t : ℝ, ∃ P : SequentialProduct J, FlowFormula P ψ t)

/-- `mthm:master` — Rank at least three has only the real twist parameter on the complex type. -/
def Master (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  Simple J → 3 ≤ rank J → ∀ P : SequentialProduct J,
    (¬ HasComplexModel J → Rigid P) ∧
      ∀ n (M : ComplexModel J n), 3 ≤ n → ∃! t : ℝ, Twist M t P.sp

/-- `mthm:omnibus` — The parameter bijection on one fixed model. -/
def SimpleParametrization (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ (ℓ : Label) (M : ModelWitness J ℓ),
    ∃ e : ProductSpace J ≃ ℓ.Param, ∀ P, ParamSpec ℓ M (e P) P

/-- `rem:dyn-existence` — Dynamical correspondences, complex models, and non-Lüders products. -/
def DynamicalEquivalence (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  Simple J → 3 ≤ rank J →
    ((∃ P : SequentialProduct J, ¬ Rigid P) ↔ Nonempty (DynamicalCorrespondence J)) ∧
      (Nonempty (DynamicalCorrespondence J) ↔ HasComplexModel J)

/-- `mthm:dyn` — The flow formula for a twisted product on an invertible effect. -/
def DynamicalForm (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ {n : ℕ} (M : ComplexModel J n), 3 ≤ n → ∀ (ψ : DynamicalCorrespondence J),
    (∀ h x, M.map (ψ.psi h x) =
      (Complex.I / 2) • (M.map h * M.map x - M.map x * M.map h)) →
    ∀ (P : SequentialProduct J) (t : ℝ), Twist M t P.sp →
      ∀ a b : J, IsEffect a → StrictPositive a → IsEffect b →
        ∀ D : J →L[ℝ] J, (∀ x, D x = ψ.psi (log a) x) →
          P.sp a b = Q (sqrt a) (NormedSpace.exp ((2 * t) • D) b)

/-- `rem:dyn-rank-two` — Rank-two separation of dynamical correspondences
and non-Lüders products. -/
def DynamicalRankTwo (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ {d : ℕ}, SpinModel J d → 2 ≤ d → d ≠ 3 →
    ¬ Nonempty (DynamicalCorrespondence J) ∧
      (4 ≤ d → ∃ P : SequentialProduct J, ¬ Rigid P)

/-- `thm:complex` — Uniqueness and existence of the complex twist parameter. -/
def ComplexClassification (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ (P : SequentialProduct J) {n : ℕ} (M : ComplexModel J n),
    3 ≤ n → ∃! t : ℝ, Twist M t P.sp

/-- `thm:spin` — Existence and spherical uniqueness of the spin axis field. -/
def SpinClassification (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ (P : SequentialProduct J) {d : ℕ} (M : SpinModel J d), 2 ≤ d →
    ∃ A : AxisField d, Agrees P.sp (spinOn M A) ∧
      ∀ B : AxisField d, Agrees P.sp (spinOn M B) → FieldEq B A

/-- `cor:qubit-classification` — Classification by a continuous frame function. -/
def QubitClassification (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ (P : SequentialProduct J) (M : SpinModel J 3),
    ∃! t : C(RP2, ℝ), Agrees P.sp (spinOn M (fieldOfFrameFunction t))

/-- `lem:twist-sufficiency` — Every complex twist satisfies the axioms. -/
def TwistSufficiency (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ {n : ℕ} (M : ComplexModel J n), 2 ≤ n → ∀ t : ℝ,
    ∃ P : SequentialProduct J, Twist M t P.sp

/-- `mthm:omnibus` — The Lüders product satisfies the axioms. -/
def LudersSufficiency (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∃ P : SequentialProduct J, Agrees P.sp luders

/-- `thm:spin` — Every axis field gives a product. -/
def SpinSufficiency (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ {d : ℕ} (M : SpinModel J d), 2 ≤ d → ∀ A : AxisField d,
    ∃ P : SequentialProduct J, Agrees P.sp (spinOn M A)

/-- `thm:rigid` — Rigidity on the specified real, quaternionic, and exceptional types. -/
def Rigidity (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ P : SequentialProduct J, ((∃ n, 2 ≤ n ∧ Nonempty (RealModel J n)) ∨
    (∃ n, 3 ≤ n ∧ Nonempty (QuaternionModel J n)) ∨ Nonempty (AlbertModel J)) → Rigid P

/-- `sec:eja` — The Jordan–von Neumann–Wigner model list. -/
def JordanClassification (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  Simple J → ∃ ℓ : Label, Realizes J ℓ

/-- `rem:moduli` — The labelled complex parameter bijection. -/
def Moduli (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  ∀ {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n),
    ∃ e : ProductSpace J ≃ ℝ, ∀ P, ParamSpec (.complex n hn) M (e P) P

/-- `sec:eja` — Existence of the decomposition into simple summands. -/
def SimpleDecomposition (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  Nonempty (Decomposition J)

/-- `cor:qubit-classification` — The qubit fields are parametrized by
continuous functions on the space of unoriented axes. -/
def QubitField : Prop :=
  ∃ e : FieldSpace 3 ≃ C(RP2, ℝ), ∀ A : AxisField 3,
    FrameFunctionSpec (e (Quotient.mk (FieldSetoid 3) A)) A

/-- `sec:eja` — Every element admits a complete spectral resolution. -/
def SpectralResolution (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] : Prop :=
  ∀ a : J, Nonempty (Resolution a)

/-- The conjunction of the manuscript’s main statements and their classification clauses. -/
def Conclusions (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Prop :=
  Omnibus J ∧
  Master J ∧
  DynamicalFlow J ∧
  SimpleParametrization J ∧
  DynamicalEquivalence J ∧
  DynamicalForm J ∧
  DynamicalRankTwo J ∧
  ComplexClassification J ∧
  SpinClassification J ∧
  QubitClassification J ∧
  TwistSufficiency J ∧
  LudersSufficiency J ∧
  SpinSufficiency J ∧
  Rigidity J ∧
  JordanClassification J ∧
  Moduli J ∧
  SimpleDecomposition J ∧
  QubitField ∧
  SpectralResolution J

/-- Paper A, including the three manuscript main theorems. -/
theorem paperA (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] : Conclusions J := by
  sorry

end PaperA.Statement

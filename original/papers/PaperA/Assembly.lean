import PaperA.Definitions
import Mathlib.Topology.ContinuousMap.Basic

noncomputable section
open scoped BigOperators
open EuclideanJordan
namespace PaperA

structure Object where
  V : Type
  [normed : NormedAddCommGroup V]
  [inner : InnerProductSpace ℝ V]
  [jordan : EuclideanJordanAlgebra V]
  [finite : FiniteDimensional ℝ V]
attribute [instance] Object.normed Object.inner Object.jordan Object.finite

variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J]

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
    simp only [ContinuousLinearMap.smul_apply, real_inner_smul_right,
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
def componentEffect (D : Decomposition J) (a : Effects J) (i : Fin D.n) :
    Effects (D.blocks i).V := by
  refine ⟨D.equiv a.val i, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := a.property.1
    exact ⟨D.equiv x i, (D.mul x x i).symm.trans (congrArg (fun v => D.equiv v i) hx)⟩
  · obtain ⟨x, hx⟩ := a.property.2
    refine ⟨D.equiv x i, ?_⟩
    rw [← D.mul, hx, map_sub, Pi.sub_apply, D.unit]
def restrictProducts (D : Decomposition J) : ProductSpace J ≃
    (∀ i, ProductSpace (D.blocks i).V) := by sorry

def FrameTwist {n m : ℕ} (M : ComplexModel J n) (P : SequentialProduct J)
    (F : JordanFrame J m) (t : ℝ) : Prop :=
  ∀ a b, IsEffect a → StrictPositive a → Diagonal F.p a → IsEffect b →
    M.map (P.sp a b) = twistFactor M t a * M.map b * (twistFactor M t a).conjTranspose
def Adjacent {n : ℕ} (F G : JordanFrame J n) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ F.p i+F.p j = G.p i+G.p j ∧
    ∀ k, k ≠ i → k ≠ j → F.p k = G.p k
def CrossSpace {n : ℕ} (q p : Matrix (Fin n) (Fin n) ℂ) :=
  {x : Matrix (Fin n) (Fin n) ℂ | x.conjTranspose = x ∧ x = q*x*p+p*x*q}
def CrossJ {n : ℕ} (q p x : Matrix (Fin n) (Fin n) ℂ) :=
  Complex.I • (q*x*p) - Complex.I • (q*x*p).conjTranspose
def detection (t r φ : ℝ) : ℝ :=
  (1+Real.exp (-r))/4 + Real.exp (-r/2)/2 * Real.cos (φ-t*r)
def detectionA (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.exp (-r) : ℂ), 0; 0, 1]
def detectionB : Matrix (Fin 2) (Fin 2) ℂ := !![1/2,1/2;1/2,1/2]
def detectionRho (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1/2, Complex.exp (-Complex.I*φ)/2; Complex.exp (Complex.I*φ)/2, 1/2]
def detectionFactor (t r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp ((-(r/2) : ℝ) - Complex.I*(t*r)),0;0,1]

end PaperA

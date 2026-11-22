import PaperA.Statement
import PaperA.Claims

/-! Transport between the standalone statement and the existing claim vocabulary. -/

noncomputable section
open scoped BigOperators
namespace PaperA.StatementBridge

variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- The two Jordan classes carry the same operations and laws. -/
abbrev fromLibraryJordan (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordan.EuclideanJordanAlgebra J] : Statement.EuclideanJordanAlgebra J :=
  { ‹EuclideanJordan.EuclideanJordanAlgebra J› with }

abbrev toLibraryJordan (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [Statement.EuclideanJordanAlgebra J] : EuclideanJordan.EuclideanJordanAlgebra J :=
  { ‹Statement.EuclideanJordanAlgebra J› with }

section
variable [EuclideanJordan.EuclideanJordanAlgebra J]
attribute [local instance] fromLibraryJordan

theorem positive_iff (a : J) : Statement.Positive a ↔ Positive a := Iff.rfl
theorem below_iff (a b : J) : Statement.Below a b ↔ Below a b := Iff.rfl
theorem effect_iff (a : J) : Statement.IsEffect a ↔ IsEffect a := Iff.rfl
theorem effects_eq : Statement.Effects J = Effects J := rfl
theorem idempotent_iff (p : J) : Statement.Idempotent p ↔ Idempotent p := Iff.rfl
theorem primitive_iff (p : J) : Statement.Primitive p ↔ Primitive p := Iff.rfl
omit [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordan.EuclideanJordanAlgebra J] in
theorem compatible_iff (f : J → J → J) (a b : J) :
    Statement.Compatible f a b ↔ Compatible f a b := Iff.rfl
theorem strictPositive_iff (a : J) : Statement.StrictPositive a ↔ StrictPositive a := Iff.rfl
theorem ouNorm_eq (a : J) : Statement.ouNorm a = ouNorm a := rfl
theorem ideal_iff (I : Submodule ℝ J) : Statement.Ideal I ↔ Ideal I := Iff.rfl
theorem simple_iff : Statement.Simple J ↔ Simple J := Iff.rfl
theorem q_eq (a b : J) : Statement.Q a b = Q a b := rfl
theorem derivation_iff (D : J →ₗ[ℝ] J) : Statement.Derivation D ↔ Derivation D := Iff.rfl

theorem rank_eq : Statement.rank J = EuclideanJordan.rank J := by
  unfold Statement.rank EuclideanJordan.rank EuclideanJordan.orthIdemCards
  congr 1
  ext n
  constructor
  · rintro ⟨p, hi, ho, hn⟩
    exact ⟨p, ⟨hi, ho⟩, hn⟩
  · rintro ⟨p, ⟨hi, ho⟩, hn⟩
    exact ⟨p, hi, ho, hn⟩

def resolution (a : J) (R : Resolution a) : Statement.Resolution a :=
  ⟨R.n, R.frame.p, R.frame.orthIdem.idem, R.frame.orthIdem.orth, R.frame.complete,
    R.eigenvalue, R.equation⟩

variable [FiniteDimensional ℝ J]

theorem cfc_eq (f : ℝ → ℝ) (a : J) : Statement.cfc f a = cfc f a :=
  Statement.cfc_eq (resolution a (resolve a)) f

theorem sqrt_eq (a : J) : Statement.sqrt a = sqrt a := cfc_eq _ a
theorem inverseSqrt_eq (a : J) : Statement.inverseSqrt a = inverseSqrt a := cfc_eq _ a
theorem log_eq (a : J) : Statement.log a = log a := cfc_eq _ a
theorem support_eq (a : J) : Statement.support a = support a := cfc_eq _ a
theorem luders_eq (a b : J) : Statement.luders a b = luders a b := by
  rw [Statement.luders, sqrt_eq, q_eq, luders]

/-- The guarded products have identical data and laws. -/
def productEquiv : Statement.SequentialProduct J ≃ SequentialProduct J where
  toFun P := ⟨P.sp, P.closed, P.S1, P.S2, P.S3, P.S4, P.S5, P.S6_compl, P.S6_sum, P.S7⟩
  invFun P := ⟨P.sp, P.closed, P.S1, P.S2, P.S3, P.S4, P.S5, P.S6_compl, P.S6_sum, P.S7⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [FiniteDimensional ℝ J] in
theorem agrees_iff (f g : J → J → J) : Statement.Agrees f g ↔ Agrees f g := Iff.rfl

theorem leftMap_eq (P : Statement.SequentialProduct J) (a : J) :
    Statement.leftMap P a = leftMap (productEquiv P) a := by
  classical
  by_cases ha : IsEffect a
  · have h := leftMap_spec (productEquiv P) a ha
    have hex : ∃ L : J →L[ℝ] J, (∀ b, Statement.IsEffect b → L b = P.sp a b) ∧
        (∀ x, Statement.Positive x → Statement.Positive (L x)) :=
      ⟨_, h.1, h.2.1⟩
    have hae : Statement.IsEffect a := ha
    rw [Statement.leftMap, if_pos hae, dif_pos hex]
    exact h.2.2 _ hex.choose_spec.1
  · have hae : ¬ Statement.IsEffect a := ha
    simp only [Statement.leftMap, leftMap, if_neg hae, dif_neg ha]

theorem theta_eq (P : Statement.SequentialProduct J) (a x : J) :
    Statement.theta P a x = theta (productEquiv P) a x := by
  rw [Statement.theta, inverseSqrt_eq, leftMap_eq, q_eq, theta]

theorem rigid_iff (P : Statement.SequentialProduct J) :
    Statement.Rigid P ↔ Rigid (productEquiv P) := by
  simp only [Statement.Rigid, Rigid, Statement.Agrees, Agrees, luders_eq]
  rfl

theorem oct_eq : Statement.Oct = Oct := rfl
theorem octConj_eq (x : Oct) : Statement.octConj x = octConj x := rfl
theorem octMul_eq (x y : Oct) : Statement.octMul x y = octMul x y := rfl
theorem octOne_eq : Statement.octOne = octOne := rfl

theorem rawMatMul_eq {K : Type} [AddCommMonoid K] {n : ℕ} (m : K → K → K)
    (a b : Matrix (Fin n) (Fin n) K) : Statement.rawMatMul m a b = rawMatMul m a b := rfl

def matrixEquiv {K : Type} [AddCommGroup K] [Module ℝ K] {mul : K → K → K}
    {conj : K → K} {one : K} {n : ℕ} :
    Statement.MatrixModel J K mul conj one n ≃ MatrixModel J K mul conj one n where
  toFun M := ⟨M.map, M.injective, M.range, M.unit, M.product⟩
  invFun M := ⟨M.map, M.injective, M.range, M.unit, M.product⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [FiniteDimensional ℝ J] in
theorem complexModel_iff : Statement.HasComplexModel J ↔ HasComplexModel J := by
  constructor
  · rintro ⟨n, hn, ⟨M⟩⟩
    exact ⟨n, hn, ⟨matrixEquiv M⟩⟩
  · rintro ⟨n, hn, ⟨M⟩⟩
    exact ⟨n, hn, ⟨matrixEquiv.symm M⟩⟩

theorem twistFactor_eq {n : ℕ} (M : Statement.ComplexModel J n) (t : ℝ) (a : J) :
    Statement.twistFactor M t a = twistFactor (matrixEquiv M) t a := by
  simp only [Statement.twistFactor, twistFactor, cfc_eq]
  rfl

theorem phaseUnit_eq {n : ℕ} (M : Statement.ComplexModel J n) (t : ℝ) (a : J) :
    Statement.phaseUnit M t a = phaseUnit (matrixEquiv M) t a := by
  simp only [Statement.phaseUnit, phaseUnit, support_eq, cfc_eq]
  rfl

theorem twist_iff {n : ℕ} (M : Statement.ComplexModel J n) (t : ℝ) (f : J → J → J) :
    Statement.Twist M t f ↔ Twist (matrixEquiv M) t f := by
  simp only [Statement.Twist, Twist, twistFactor_eq]
  rfl

def dynamicsEquiv : Statement.DynamicalCorrespondence J ≃ DynamicalCorrespondence J where
  toFun D := ⟨D.psi, D.derivation, D.fixes, D.bracket⟩
  invFun D := ⟨D.psi, D.derivation, D.fixes, D.bracket⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem vec_eq (d : ℕ) : Statement.Vec d = Vec d := rfl
theorem spin_eq (d : ℕ) : Statement.Spin d = Spin d := rfl
theorem sphere_eq (d : ℕ) : Statement.sphere d = sphere d := rfl
theorem spinMul_eq {d : ℕ} (a b : Spin d) : Statement.spinMul a b = spinMul a b := rfl
theorem spinUnit_eq (d : ℕ) : Statement.spinUnit d = spinUnit d := rfl
theorem spinAtom_eq {d : ℕ} (v : Vec d) : Statement.spinAtom v = spinAtom v := rfl
theorem spinPositive_iff {d : ℕ} (a : Spin d) :
    Statement.spinPositive a ↔ spinPositive a := Iff.rfl
theorem spinEffect_iff {d : ℕ} (a : Spin d) :
    Statement.spinEffect a ↔ spinEffect a := Iff.rfl

def spinModelEquiv {d : ℕ} : Statement.SpinModel J d ≃ SpinModel J d where
  toFun M := ⟨M.equiv, M.unit, M.mul⟩
  invFun M := ⟨M.equiv, M.unit, M.mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

def axisEquiv (d : ℕ) : Statement.AxisField d ≃ AxisField d where
  toFun A := ⟨A.A, A.continuous, A.skew, A.fixes, A.odd⟩
  invFun A := ⟨A.A, A.continuous, A.skew, A.fixes, A.odd⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fieldEq_iff {d : ℕ} (A B : Statement.AxisField d) :
    Statement.FieldEq A B ↔ FieldEq (axisEquiv d A) (axisEquiv d B) := Iff.rfl

def fieldSpaceEquiv (d : ℕ) : Statement.FieldSpace d ≃ FieldSpace d :=
  Quotient.congr (axisEquiv d) (fieldEq_iff · ·)

theorem spinRotation_eq {d : ℕ} (A : Statement.AxisField d) (a : Statement.Spin d) :
    Statement.spinRotation A a = spinRotation (axisEquiv d A) a := rfl

theorem spinProduct_eq {d : ℕ} (A : Statement.AxisField d) (a b : Statement.Spin d) :
    Statement.spinProduct A a b = spinProduct (axisEquiv d A) a b := rfl

omit [FiniteDimensional ℝ J] in
theorem spinOn_eq {d : ℕ} (M : Statement.SpinModel J d) (A : Statement.AxisField d)
    (a b : J) : Statement.spinOn M A a b = spinOn (spinModelEquiv M) (axisEquiv d A) a b := rfl

theorem antipodal_eq : Statement.Antipodal = Antipodal := rfl
theorem rp2_eq : Statement.RP2 = RP2 := rfl
theorem rp2Topology_eq : Statement.rp2Topology = rp2Topology := rfl
theorem rp2Class_eq (v : sphere 3) : Statement.rp2Class v = rp2Class v := rfl

theorem frameFunction_eq (t : C(Statement.RP2, ℝ)) :
    axisEquiv 3 (Statement.fieldOfFrameFunction t) = fieldOfFrameFunction t := rfl

theorem frameFunctionSpec_iff (t : C(Statement.RP2, ℝ)) (A : Statement.AxisField 3) :
    Statement.FrameFunctionSpec t A ↔ FrameFunctionSpec t (axisEquiv 3 A) := Iff.rfl

/-- The quotient by off-effect values has the same underlying operation. -/
def productSpaceEquiv : Statement.ProductSpace J ≃ ProductSpace J :=
  Equiv.subtypeEquivRight fun _ => ⟨
    fun ⟨P, h⟩ => ⟨productEquiv P, h⟩,
    fun ⟨P, h⟩ => ⟨productEquiv.symm P, h⟩⟩

def labelEquiv : Statement.Label ≃ Label where
  toFun
    | .scalar => .scalar
    | .real n h => .real n h
    | .complex n h => .complex n h
    | .quaternion n h => .quaternion n h
    | .albert => .albert
    | .spin d h => .spin d h
  invFun
    | .scalar => .scalar
    | .real n h => .real n h
    | .complex n h => .complex n h
    | .quaternion n h => .quaternion n h
    | .albert => .albert
    | .spin d h => .spin d h
  left_inv ℓ := by cases ℓ <;> rfl
  right_inv ℓ := by cases ℓ <;> rfl

def paramEquiv (ℓ : Statement.Label) : ℓ.Param ≃ (labelEquiv ℓ).Param :=
  match ℓ with
  | .scalar | .real .. | .quaternion .. | .albert => Equiv.refl Unit
  | .complex .. => Equiv.refl ℝ
  | .spin d _ => fieldSpaceEquiv d

def modelEquiv (ℓ : Statement.Label) :
    Statement.ModelWitness J ℓ ≃ ModelWitness J (labelEquiv ℓ) :=
  match ℓ with
  | .scalar | .real .. | .complex .. | .quaternion .. | .albert => matrixEquiv
  | .spin .. => spinModelEquiv

omit [FiniteDimensional ℝ J] in
theorem realizes_iff (ℓ : Statement.Label) :
    Statement.Realizes J ℓ ↔ Realizes J (labelEquiv ℓ) := by
  have h : Nonempty (Statement.ModelWitness J ℓ) ↔
      Nonempty (ModelWitness J (labelEquiv ℓ)) :=
    ⟨fun ⟨M⟩ => ⟨modelEquiv ℓ M⟩, fun ⟨M⟩ => ⟨(modelEquiv ℓ).symm M⟩⟩
  cases ℓ <;> exact h

theorem paramSpec_iff (ℓ : Statement.Label) (M : Statement.ModelWitness J ℓ)
    (t : ℓ.Param) (P : Statement.ProductSpace J) :
    Statement.ParamSpec ℓ M t P ↔
      ParamSpec (labelEquiv ℓ) (modelEquiv ℓ M) (paramEquiv ℓ t) (productSpaceEquiv P) := by
  cases ℓ with
  | scalar | real | quaternion | albert =>
      simp only [Statement.ParamSpec, ParamSpec, labelEquiv, luders_eq]
      rfl
  | complex n hn =>
      let N : Statement.ComplexModel J n := M
      let u : ℝ := t
      let f : Statement.Effects J → Statement.Effects J → Statement.Effects J := P.val
      change (∀ a b : Statement.Effects J, N.map ((f a b).val) =
        Statement.twistFactor N u a.val * N.map b.val *
          (Statement.twistFactor N u a.val).conjTranspose) ↔
        (∀ a b : Statement.Effects J, (matrixEquiv N).map ((f a b).val) =
          twistFactor (matrixEquiv N) u a.val * (matrixEquiv N).map b.val *
            (twistFactor (matrixEquiv N) u a.val).conjTranspose)
      constructor <;> intro h a b
      · have he := h a b
        rw [twistFactor_eq] at he
        exact he
      · rw [twistFactor_eq]
        exact h a b
  | spin d hd =>
      constructor
      · rintro ⟨A, hA, h⟩
        refine ⟨axisEquiv d A, congrArg (fieldSpaceEquiv d) hA, fun a b => ?_⟩
        exact (h a b).trans (spinOn_eq M A a.val b.val)
      · rintro ⟨A, hA, h⟩
        let B := (axisEquiv d).symm A
        have hB : axisEquiv d B = A := (axisEquiv d).apply_symm_apply A
        refine ⟨B, (fieldSpaceEquiv d).injective ?_, fun a b => ?_⟩
        · change Quotient.mk (FieldSetoid d) (axisEquiv d B) = fieldSpaceEquiv d t
          rw [hB]
          exact hA
        · calc
            (P.val a b).val = spinOn (spinModelEquiv M) A a.val b.val := h a b
            _ = Statement.spinOn M B a.val b.val := by
              rw [spinOn_eq M B a.val b.val, hB]

def toLibraryObject (B : Statement.Object) : Object where
  V := B.V
  normed := B.normed
  inner := B.inner
  jordan := @toLibraryJordan B.V B.normed B.inner B.jordan
  finite := B.finite

def fromLibraryObject (B : Object) : Statement.Object where
  V := B.V
  normed := B.normed
  inner := B.inner
  jordan := @fromLibraryJordan B.V B.normed B.inner B.jordan
  finite := B.finite

def objectEquiv : Statement.Object ≃ Object where
  toFun := toLibraryObject
  invFun := fromLibraryObject
  left_inv _ := rfl
  right_inv _ := rfl

def decompositionEquiv : Statement.Decomposition J ≃ Decomposition J where
  toFun D := ⟨D.n, fun i => toLibraryObject (D.blocks i), D.simple, D.equiv, D.unit, D.mul⟩
  invFun D := ⟨D.n, fun i => fromLibraryObject (D.blocks i), D.simple, D.equiv, D.unit, D.mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [FiniteDimensional ℝ J] in
theorem componentEffect_eq (D : Statement.Decomposition J) (a : Statement.Effects J)
    (i : Fin D.n) : Statement.componentEffect D a i =
      componentEffect (decompositionEquiv D) a i := by
  apply Subtype.ext
  rfl


/-- The claim interfaces used in the bridge. Restriction is supplied along with its
coordinate law so that the transport can be checked independently of proof debt. -/
structure ClaimsFor (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordan.EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] where
  restrict (D : Decomposition J) : ProductSpace J ≃
    (∀ i, ProductSpace (D.blocks i).V)
  central (D : Decomposition J) (P : ProductSpace J) (a b : Effects J) (i : Fin D.n) :
    D.equiv (P.val a b).val i =
      (((restrict D P) i).val (componentEffect D a i) (componentEffect D b i)).val
  omnibus (D : Decomposition J) (ℓ : Fin D.n → Label)
      (M : ∀ i, ModelWitness (D.blocks i).V (ℓ i)) :
    ∃ e : ProductSpace J ≃ (∀ i, (ℓ i).Param), ∀ P i,
      ParamSpec (ℓ i) (M i) (e P i) ((restrict D P) i)
  master : type_of% (@PaperA.master J _ _ _ _)
  simple_parametrization : type_of% (@PaperA.simple_parametrization J _ _ _ _)
  dyn_equivalence : type_of% (@PaperA.dyn_equivalence J _ _ _ _)
  dyn_form : type_of% (@PaperA.dyn_form J _ _ _ _)
  dyn_rank_two : type_of% (@PaperA.dyn_rank_two J _ _ _ _)
  complex_classification : type_of% (@PaperA.complex_classification J _ _ _ _)
  spin_classification : type_of% (@PaperA.spin_classification J _ _ _ _)
  qubit_classification : type_of% (@PaperA.qubit_classification J _ _ _ _)
  twist_sufficiency : type_of% (@PaperA.twist_sufficiency J _ _ _ _)
  luders_sufficiency : type_of% (@PaperA.luders_sufficiency J _ _ _ _)
  spin_sufficiency : type_of% (@PaperA.spin_sufficiency J _ _ _ _)
  rigid : type_of% (@PaperA.rigid J _ _ _ _)
  jvnw : type_of% (@PaperA.jvnw J _ _ _ _)
  moduli : type_of% (@PaperA.moduli J _ _ _ _)
  simple_decomposition : type_of% (@PaperA.simple_decomposition J _ _ _ _)
  qubit_field : type_of% (PaperA.qubit_field)
  qubit_field_constructor : type_of% (PaperA.qubit_field_constructor)
  dynamical_matrix : type_of% (@PaperA.dynamical_matrix J _ _ _ _)
  singular_twist : type_of% (@PaperA.singular_twist J _ _ _ _)

private theorem nonrigid_iff :
    (∃ P : Statement.SequentialProduct J, ¬ Statement.Rigid P) ↔
    (∃ P : SequentialProduct J, ¬ Rigid P) := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨productEquiv P, hP ∘ (rigid_iff P).mpr⟩
  · rintro ⟨P, hP⟩
    refine ⟨productEquiv.symm P, ?_⟩
    simpa only [rigid_iff, Equiv.apply_symm_apply] using hP

omit [FiniteDimensional ℝ J] in
private theorem dynamics_iff :
    Nonempty (Statement.DynamicalCorrespondence J) ↔ Nonempty (DynamicalCorrespondence J) :=
  ⟨fun ⟨ψ⟩ => ⟨dynamicsEquiv ψ⟩, fun ⟨ψ⟩ => ⟨dynamicsEquiv.symm ψ⟩⟩

private theorem spin_agrees_iff {d : ℕ} (P : Statement.SequentialProduct J)
    (M : Statement.SpinModel J d) (A : Statement.AxisField d) :
    Statement.Agrees P.sp (Statement.spinOn M A) ↔
      Agrees (productEquiv P).sp (spinOn (spinModelEquiv M) (axisEquiv d A)) := by
  simp only [Statement.Agrees, Agrees, spinOn_eq]
  rfl

private theorem transferOmnibus (H : ClaimsFor J) : Statement.Omnibus J := by
  intro D ℓ M
  let E := decompositionEquiv D
  let labels : Fin E.n → Label := fun i => labelEquiv (ℓ i)
  let models (i : Fin E.n) : ModelWitness (E.blocks i).V (labels i) := modelEquiv (ℓ i) (M i)
  let products := Equiv.piCongrRight fun i : Fin E.n =>
    productSpaceEquiv (J := (E.blocks i).V)
  let params := Equiv.piCongrRight (fun i : Fin E.n => paramEquiv (ℓ i))
  let R := productSpaceEquiv.trans ((H.restrict E).trans products.symm)
  obtain ⟨e, he⟩ := H.omnibus E labels models
  refine ⟨R, ?_, (productSpaceEquiv.trans e).trans params.symm, ?_⟩
  · intro P a b i
    exact H.central E (productSpaceEquiv P) a b i
  · intro P i
    let N : Statement.ModelWitness (E.blocks i).V (ℓ i) := M i
    let e₀ := e (productSpaceEquiv P) i
    let P₀ := H.restrict E (productSpaceEquiv P) i
    change Statement.ParamSpec (ℓ i) N ((paramEquiv (ℓ i)).symm e₀)
      (productSpaceEquiv.symm P₀)
    apply (paramSpec_iff (ℓ i) N _ _).mpr
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact he (productSpaceEquiv P) i

private theorem transferMaster (H : ClaimsFor J) : Statement.Master J := by
  intro hJ hr P
  rw [rank_eq] at hr
  obtain ⟨h₁, h₂⟩ := H.master hJ hr (productEquiv P)
  refine ⟨fun h => (rigid_iff P).mpr (h₁ (h ∘ complexModel_iff.mpr)), ?_⟩
  intro n M hn
  exact (existsUnique_congr (fun t => twist_iff M t P.sp)).mpr (h₂ n (matrixEquiv M) hn)

private theorem transferDynamicalForm (H : ClaimsFor J) : Statement.DynamicalForm J := by
  intro n M hn ψ hψ P t ht a b ha hi hb D hD
  rw [StatementBridge.log_eq] at hD
  rw [StatementBridge.q_eq, StatementBridge.sqrt_eq]
  exact H.dyn_form (matrixEquiv M) hn (dynamicsEquiv ψ) hψ (productEquiv P)
    t ((twist_iff M t _).mp ht) a b ha hi hb D hD

private theorem transferComplexClassification (H : ClaimsFor J) :
    Statement.ComplexClassification J := by
  intro P n M hn
  exact (existsUnique_congr (fun t => twist_iff M t P.sp)).mpr
    (H.complex_classification (productEquiv P) (matrixEquiv M) hn)

private theorem transferTwistSufficiency (H : ClaimsFor J) : Statement.TwistSufficiency J := by
  intro n M hn t
  obtain ⟨P, hP⟩ := H.twist_sufficiency (matrixEquiv M) hn t
  exact ⟨productEquiv.symm P, (twist_iff M t _).mpr hP⟩

private theorem transferDynamicalFlow (H : ClaimsFor J) : Statement.DynamicalFlow J := by
  intro n M hn
  obtain ⟨ψ₀, hψ⟩ := H.dynamical_matrix (matrixEquiv M)
  let ψ := dynamicsEquiv.symm ψ₀
  have forward (P : Statement.SequentialProduct J) (t : ℝ) (ht : Statement.Twist M t P.sp) :
      Statement.FlowFormula P ψ t := by
    intro a b ha hi hb
    exact transferDynamicalForm H M hn ψ hψ P t ht a b ha hi hb _ (fun _ => rfl)
  have eqv (P : Statement.SequentialProduct J) (t : ℝ) :
      Statement.FlowFormula P ψ t ↔ Statement.Twist M t P.sp := by
    refine ⟨?_, forward P t⟩
    intro h
    obtain ⟨Pₜ, ht⟩ := transferTwistSufficiency H M (by omega) t
    apply (twist_iff M t _).mpr
    apply H.singular_twist (productEquiv P) (matrixEquiv M) t
    intro a b ha hi hb
    have hp : P.sp a b = Pₜ.sp a b :=
      (h a b ha hi hb).trans ((forward Pₜ t ht) a b ha hi hb).symm
    change (matrixEquiv M).map (P.sp a b) = _
    rw [hp]
    exact (twist_iff M t _).mp ht a b ha hb
  refine ⟨ψ, hψ, eqv, ?_, ?_⟩
  · intro P
    simpa only [eqv] using transferComplexClassification H P M hn
  · intro t
    obtain ⟨P, hP⟩ := transferTwistSufficiency H M (by omega) t
    exact ⟨P, (eqv P t).mpr hP⟩

private theorem transferQubitField (H : ClaimsFor J) : Statement.QubitField := by
  have existsUniqueSpec (A : Statement.AxisField 3) :
      ∃! t : C(Statement.RP2, ℝ), Statement.FrameFunctionSpec t A :=
    (existsUnique_congr (fun t => frameFunctionSpec_iff t A)).mpr
      (H.qubit_field (axisEquiv 3 A))
  have constructorSpec (t : C(Statement.RP2, ℝ)) :
      Statement.FrameFunctionSpec t (Statement.fieldOfFrameFunction t) := by
    apply (frameFunctionSpec_iff _ _).mpr
    rw [frameFunction_eq]
    exact H.qubit_field_constructor t
  let parameter (A : Statement.AxisField 3) := (existsUniqueSpec A).exists.choose
  have spec (A : Statement.AxisField 3) : Statement.FrameFunctionSpec (parameter A) A :=
    (existsUniqueSpec A).exists.choose_spec
  have uniq (A : Statement.AxisField 3) (t : C(Statement.RP2, ℝ))
      (ht : Statement.FrameFunctionSpec t A) : t = parameter A :=
    (existsUniqueSpec A).unique ht (spec A)
  let readParam : Statement.FieldSpace 3 → C(Statement.RP2, ℝ) :=
    Quotient.lift parameter fun A B h => by
      apply uniq B
      intro v w
      rw [← h v.val v.property]
      exact spec A v w
  refine ⟨{ toFun := readParam
            invFun := fun t => Quotient.mk _ (Statement.fieldOfFrameFunction t)
            left_inv := ?_
            right_inv := fun t => (uniq _ t (constructorSpec t)).symm }, spec⟩
  intro q
  refine Quotient.inductionOn q fun A => Quotient.sound ?_
  intro v hv
  apply ContinuousLinearMap.ext
  intro w
  exact (constructorSpec (parameter A) ⟨v, hv⟩ w).trans (spec A ⟨v, hv⟩ w).symm

/-- The standalone conjunction follows from the existing claim signatures. -/
theorem bridge (H : ClaimsFor J) : Statement.Conclusions J := by
  refine ⟨transferOmnibus H, transferMaster H, transferDynamicalFlow H, ?_, ?_,
    transferDynamicalForm H, ?_, transferComplexClassification H, ?_, ?_,
    transferTwistSufficiency H, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ M
    obtain ⟨e, he⟩ := H.simple_parametrization (labelEquiv ℓ) (modelEquiv ℓ M)
    refine ⟨(productSpaceEquiv.trans e).trans (paramEquiv ℓ).symm, fun P => ?_⟩
    apply (paramSpec_iff ℓ M _ P).mpr
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using he (productSpaceEquiv P)
  · intro hJ hr
    rw [rank_eq] at hr
    rw [nonrigid_iff, dynamics_iff, complexModel_iff]
    exact H.dyn_equivalence hJ hr
  · intro d M hd hne
    rw [dynamics_iff, nonrigid_iff]
    exact H.dyn_rank_two (spinModelEquiv M) hd hne
  · intro P d M hd
    obtain ⟨A, hA, hu⟩ := H.spin_classification (productEquiv P) (spinModelEquiv M) hd
    use (axisEquiv d).symm A
    refine ⟨(spin_agrees_iff P M _).mpr (by simpa only [Equiv.apply_symm_apply] using hA),
      fun B hB => (fieldEq_iff _ _).mpr ?_⟩
    simpa only [Equiv.apply_symm_apply] using hu _ ((spin_agrees_iff P M B).mp hB)
  · intro P M
    have h (t : C(Statement.RP2, ℝ)) : Statement.Agrees P.sp
        (Statement.spinOn M (Statement.fieldOfFrameFunction t)) ↔
        Agrees (productEquiv P).sp (spinOn (spinModelEquiv M) (fieldOfFrameFunction t)) := by
      rw [spin_agrees_iff, frameFunction_eq]
    exact (existsUnique_congr h).mpr (H.qubit_classification (productEquiv P) (spinModelEquiv M))
  · obtain ⟨P, hP⟩ := H.luders_sufficiency
    refine ⟨productEquiv.symm P, fun a b ha hb => ?_⟩
    exact (hP a b ha hb).trans (luders_eq a b).symm
  · intro d M hd A
    obtain ⟨P, hP⟩ := H.spin_sufficiency (spinModelEquiv M) hd (axisEquiv d A)
    exact ⟨productEquiv.symm P, (spin_agrees_iff _ M A).mpr (by
      simpa only [Equiv.apply_symm_apply] using hP)⟩
  · intro P h
    apply (rigid_iff P).mpr
    apply H.rigid
    rcases h with ⟨n, hn, ⟨M⟩⟩ | ⟨n, hn, ⟨M⟩⟩ | hM
    · exact Or.inl ⟨n, hn, ⟨matrixEquiv M⟩⟩
    · exact Or.inr (Or.inl ⟨n, hn, ⟨matrixEquiv M⟩⟩)
    · obtain ⟨M⟩ := hM
      exact Or.inr (Or.inr ⟨matrixEquiv M⟩)
  · intro hJ
    obtain ⟨ℓ, hℓ⟩ := H.jvnw hJ
    refine ⟨labelEquiv.symm ℓ, (realizes_iff _).mpr ?_⟩
    simpa only [Equiv.apply_symm_apply] using hℓ
  · intro n M hn
    obtain ⟨e, he⟩ := H.moduli (matrixEquiv M) hn
    refine ⟨productSpaceEquiv.trans e, fun P => ?_⟩
    exact (paramSpec_iff (.complex n hn) M _ P).mpr (he (productSpaceEquiv P))
  · obtain ⟨D⟩ := H.simple_decomposition
    exact ⟨decompositionEquiv.symm D⟩
  · exact transferQubitField H
  · intro a
    exact ⟨resolution a (resolve a)⟩

/-- Apply the transport to the current Claims. Its axioms include the Claims' proof debt. -/
theorem fromClaims : Statement.Conclusions J :=
  bridge
    { restrict := restrictProducts
      central := PaperA.central
      omnibus := PaperA.omnibus
      master := PaperA.master
      simple_parametrization := PaperA.simple_parametrization
      dyn_equivalence := PaperA.dyn_equivalence
      dyn_form := @PaperA.dyn_form J _ _ _ _
      dyn_rank_two := @PaperA.dyn_rank_two J _ _ _ _
      complex_classification := PaperA.complex_classification
      spin_classification := PaperA.spin_classification
      qubit_classification := PaperA.qubit_classification
      twist_sufficiency := @PaperA.twist_sufficiency J _ _ _ _
      luders_sufficiency := PaperA.luders_sufficiency
      spin_sufficiency := @PaperA.spin_sufficiency J _ _ _ _
      rigid := PaperA.rigid
      jvnw := PaperA.jvnw
      moduli := @PaperA.moduli J _ _ _ _
      simple_decomposition := PaperA.simple_decomposition
      qubit_field := PaperA.qubit_field
      qubit_field_constructor := PaperA.qubit_field_constructor
      dynamical_matrix := @PaperA.dynamical_matrix J _ _ _ _
      singular_twist := PaperA.singular_twist }

end

/-- Every standalone Euclidean Jordan structure is an instance of the library
vocabulary, so the Claims imply the exact type of the standalone theorem. -/
theorem paperA_from_claims [Statement.EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] :
    Statement.Conclusions J := by
  let := toLibraryJordan J
  exact fromClaims (J := J)

end PaperA.StatementBridge

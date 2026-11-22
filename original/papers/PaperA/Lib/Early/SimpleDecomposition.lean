import PaperA.Assembly
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Decomposition into simple ideals

An associative inner product makes orthogonal complements of ideals into ideals.
The projection of the ambient unit supplies an ideal's own unit, identifying the
ideal and its complement with the extreme Peirce spaces. A least-dimensional
nonzero ideal is simple; dimension induction decomposes its complement.
-/

noncomputable section
open EuclideanJordan
namespace PaperA.Lib

variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J]

/-- Associativity of the inner product makes the orthogonal complement an ideal. -/
theorem ideal_orthogonal {S : Submodule ℝ J} (hS : Ideal S) : Ideal Sᗮ := by
  intro x y hy
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro z hz
  rw [← EuclideanJordanAlgebra.inner_assoc]
  exact hy (x * z) (hS x z hz)

/-- Complementary ideals annihilate each other. -/
theorem ideal_mul_orthogonal {S : Submodule ℝ J} (hS : Ideal S)
    {x y : J} (hx : x ∈ S) (hy : y ∈ Sᗮ) : x * y = 0 := by
  have hm : x * y ∈ S := by rw [mul_comm]; exact hS y x hx
  have hn : x * y ∈ Sᗮ := ideal_orthogonal hS x y hy
  exact inner_self_eq_zero.mp ((S.mem_orthogonal _).mp hn _ hm)

/-- The projection of the ambient unit acts as the unit of an ideal. -/
theorem ideal_unit [FiniteDimensional ℝ J] {S : Submodule ℝ J} (hS : Ideal S) :
    ∃ c : J, c ∈ S ∧ c * c = c ∧ ∀ x ∈ S, c * x = x := by
  obtain ⟨c, hc, d, hd, he⟩ := S.exists_add_mem_mem_orthogonal (1 : J)
  have hu : ∀ x ∈ S, c * x = x := by
    intro x hx
    have hz : d * x = 0 := by rw [mul_comm]; exact ideal_mul_orthogonal hS hx hd
    have h := EuclideanJordanAlgebra.one_mul x
    rw [he, add_mul, hz, add_zero] at h
    exact h
  exact ⟨c, hc, hu c hc, hu⟩

/-- An ideal is the Peirce one space at its own unit. -/
theorem ideal_eq_peirceOneSub {S : Submodule ℝ J} (hS : Ideal S)
    {c : J} (hc : c ∈ S) (hi : c * c = c) (hu : ∀ x ∈ S, c * x = x) :
    S = peirceOneSub hi := by
  ext x
  constructor
  · exact fun hx => hu x hx
  · intro hx
    change c * x = x at hx
    rw [← hx, mul_comm]
    exact hS x c hc

/-- The orthogonal ideal is the zero Peirce space of the ideal unit. -/
theorem ideal_orthogonal_eq_peirceZeroSub {S : Submodule ℝ J} (hS : Ideal S)
    {c : J} (hc : c ∈ S) (hi : c * c = c) (hu : ∀ x ∈ S, c * x = x) :
    Sᗮ = peirceZeroSub hi := by
  ext x
  constructor
  · exact fun hx => ideal_mul_orthogonal hS hc hx
  · intro hx
    change c * x = 0 at hx
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [← hu y hy, EuclideanJordanAlgebra.inner_assoc, hx, inner_zero_right]

/-- A nonzero finite-dimensional algebra has an ideal minimal among nonzero ideals. -/
theorem exists_minimal_ideal [FiniteDimensional ℝ J] [Nontrivial J] :
    ∃ S : Submodule ℝ J, Ideal S ∧ S ≠ ⊥ ∧
      ∀ T : Submodule ℝ J, Ideal T → T ≠ ⊥ → T ≤ S → T = S := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Submodule ℝ J,
    Ideal S ∧ S ≠ ⊥ ∧ Module.finrank ℝ S = n
  have hex : ∃ n, P n := ⟨Module.finrank ℝ (⊤ : Submodule ℝ J),
    ⊤, (fun _ _ _ => Submodule.mem_top), top_ne_bot, rfl⟩
  obtain ⟨S, hS, hne, hr⟩ := Nat.find_spec hex
  refine ⟨S, hS, hne, fun T hT hnT hTS => ?_⟩
  by_contra hneTS
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hTS hneTS)
  have hle := Nat.find_min' hex (show P (Module.finrank ℝ T) from ⟨T, hT, hnT, rfl⟩)
  omega

/-- A subideal of a unital ideal is an ideal in the ambient algebra. -/
theorem ideal_map_peirceOneSub {c : J} (hi : c * c = c)
    (hS : Ideal (peirceOneSub hi)) {T : Submodule ℝ ↥(peirceOneSub hi)}
    (hT : Ideal T) : Ideal (T.map (peirceOneSub hi).subtype) := by
  let S := peirceOneSub hi
  intro x y hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hc : c ∈ S := hi
  have hcx : c * x ∈ S := by rw [mul_comm]; exact hS x c hc
  have hx0 : x - c * x ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [inner_sub_right, ← EuclideanJordanAlgebra.inner_assoc]
    change inner ℝ w x - inner ℝ (c * w) x = 0
    rw [show c * w = w from hw, sub_self]
  have hprod : x * (z : J) = (c * x) * (z : J) := by
    have hzero := ideal_mul_orthogonal hS z.2 hx0
    rw [mul_sub, mul_comm (z : J) x, mul_comm (z : J) (c * x)] at hzero
    exact sub_eq_zero.mp hzero
  exact ⟨(⟨c * x, hcx⟩ : S) * z, hT ⟨c * x, hcx⟩ z hz, hprod.symm⟩

/-- A minimal nonzero ideal, equipped with its own unit, is simple. -/
theorem minimal_ideal_simple {c : J} (hi : c * c = c)
    (hS : Ideal (peirceOneSub hi)) (hne : peirceOneSub hi ≠ ⊥)
    (hmin : ∀ T : Submodule ℝ J, Ideal T → T ≠ ⊥ →
      T ≤ peirceOneSub hi → T = peirceOneSub hi) : Simple ↥(peirceOneSub hi) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.mpr hne, ?_⟩
  intro T hT
  by_cases hbot : T = ⊥
  · exact Or.inl hbot
  · right
    apply Submodule.map_injective_of_injective (peirceOneSub hi).injective_subtype
    rw [Submodule.map_subtype_top]
    apply hmin _ (ideal_map_peirceOneSub hi hS hT) _ ?_
    · intro h
      apply hbot
      apply Submodule.map_injective_of_injective (peirceOneSub hi).injective_subtype
      simpa using h
    · rintro _ ⟨z, _, rfl⟩
      exact z.2

/-- Splitting at an ideal unit has no half Peirce component. -/
def idealSplitEquiv {c : J} (hi : c * c = c) (hS : Ideal (peirceOneSub hi)) :
    J ≃ₗ[ℝ] (↥(peirceOneSub hi) × ↥(peirceZeroSub hi)) where
  toFun x :=
    (⟨c * x, by
      rw [mul_comm]
      exact hS x c hi⟩,
     ⟨x - c * x, by
      change c * (x - c * x) = 0
      have hx : c * (c * x) = c * x := by
        change c * x ∈ peirceOneSub hi
        rw [mul_comm]
        exact hS x c hi
      rw [mul_sub, hx, sub_self]⟩)
  invFun yz := (yz.1 : J) + (yz.2 : J)
  left_inv x := by dsimp; abel
  right_inv yz := by
    apply Prod.ext <;> apply Subtype.ext
    · change c * ((yz.1 : J) + (yz.2 : J)) = (yz.1 : J)
      rw [mul_add, yz.1.2, yz.2.2, add_zero]
    · change (yz.1 : J) + (yz.2 : J) - c * ((yz.1 : J) + (yz.2 : J)) = (yz.2 : J)
      rw [mul_add, yz.1.2, yz.2.2, add_zero, add_sub_cancel_left]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · exact mul_add c x y
    · change x + y - c * (x + y) = (x - c * x) + (y - c * y)
      rw [mul_add]; abel
  map_smul' r x := by
    apply Prod.ext <;> apply Subtype.ext
    · exact mul_smul_comm r c x
    · change r • x - c * (r • x) = r • (x - c * x)
      rw [mul_smul_comm, smul_sub]

/-- The ideal splitting preserves the two units. -/
theorem idealSplitEquiv_unit {c : J} (hi : c * c = c) (hS : Ideal (peirceOneSub hi)) :
    idealSplitEquiv hi hS 1 = (1, 1) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [idealSplitEquiv, EuclideanJordanAlgebra.mul_one']

/-- Reassembly multiplies componentwise because the two extreme Peirce spaces annihilate. -/
theorem idealSplitEquiv_symm_mul {c : J} (hi : c * c = c)
    (hS : Ideal (peirceOneSub hi))
    (x y : ↥(peirceOneSub hi) × ↥(peirceZeroSub hi)) :
    (idealSplitEquiv hi hS).symm (x * y) =
      (idealSplitEquiv hi hS).symm x * (idealSplitEquiv hi hS).symm y := by
  change (x.1 : J) * (y.1 : J) + (x.2 : J) * (y.2 : J) =
    ((x.1 : J) + (x.2 : J)) * ((y.1 : J) + (y.2 : J))
  rw [add_mul, mul_add, mul_add,
    eigen_one_mul_zero hi x.1.2 y.2.2,
    mul_comm (x.2 : J) (y.1 : J), eigen_one_mul_zero hi y.1.2 x.2.2]
  simp

/-- The splitting is a Jordan algebra isomorphism. -/
theorem idealSplitEquiv_mul {c : J} (hi : c * c = c) (hS : Ideal (peirceOneSub hi))
    (x y : J) : idealSplitEquiv hi hS (x * y) =
      idealSplitEquiv hi hS x * idealSplitEquiv hi hS y := by
  apply (idealSplitEquiv hi hS).symm.injective
  rw [LinearEquiv.symm_apply_apply, idealSplitEquiv_symm_mul,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- A component and a finite product can be indexed by one larger finite set. -/
def prependEquiv (A : Object) {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [EuclideanJordanAlgebra K] (D : Decomposition K) :
    (A.V × K) ≃ₗ[ℝ] (∀ i : Fin (D.n + 1), ((Fin.cons A D.blocks : Fin (D.n + 1) → Object) i).V) where
  toFun x := Fin.cons x.1 (fun i => D.equiv x.2 i)
  invFun f := (f 0, D.equiv.symm (fun i => f i.succ))
  left_inv x := by
    change (x.1, D.equiv.symm (D.equiv x.2)) = x
    rw [LinearEquiv.symm_apply_apply]
  right_inv f := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change D.equiv (D.equiv.symm (fun j => f j.succ)) i = f i.succ
      exact congrFun (D.equiv.apply_symm_apply (fun j => f j.succ)) i
  map_add' x y := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change D.equiv (x.2 + y.2) i = D.equiv x.2 i + D.equiv y.2 i
      rw [map_add]; rfl
  map_smul' r x := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change D.equiv (r • x.2) i = r • D.equiv x.2 i
      rw [map_smul]; rfl

/-- Add one simple ideal to an already decomposed complementary ideal. -/
def prependDecomposition (A : Object) {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [EuclideanJordanAlgebra K] (D : Decomposition K)
    (hA : Simple A.V) (e : J ≃ₗ[ℝ] (A.V × K))
    (he1 : e 1 = (1, 1)) (hemul : ∀ x y, e (x * y) = e x * e y) : Decomposition J where
  n := D.n + 1
  blocks := Fin.cons A D.blocks
  simple := Fin.cases hA D.simple
  equiv := e.trans (prependEquiv A D)
  unit := by
    intro i
    cases i using Fin.cases with
    | zero =>
      change (e 1).1 = 1
      rw [he1]
    | succ i =>
      change D.equiv (e 1).2 i = 1
      rw [he1]
      exact D.unit i
  mul := by
    intro x y i
    cases i using Fin.cases with
    | zero =>
      change (e (x * y)).1 = (e x).1 * (e y).1
      rw [hemul]; rfl
    | succ i =>
      change D.equiv (e (x * y)).2 i = D.equiv (e x).2 i * D.equiv (e y).2 i
      rw [hemul]
      exact D.mul _ _ i

/-- The zero algebra is the empty product. -/
def emptyDecomposition [Subsingleton J] : Decomposition J where
  n := 0
  blocks := Fin.elim0
  simple := fun i => Fin.elim0 i
  equiv :=
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_add' := fun _ _ => Subsingleton.elim _ _
      map_smul' := fun _ _ => Subsingleton.elim _ _ }
  unit := fun i => Fin.elim0 i
  mul := fun _ _ i => Fin.elim0 i

/-- Dimension induction removes a minimal nonzero ideal at each step. -/
theorem simple_decomposition_of_finrank_le (N : ℕ) :
    ∀ (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
      [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J],
      Module.finrank ℝ J ≤ N → Nonempty (Decomposition J) := by
  induction N with
  | zero =>
    intro J _ _ _ _ hN
    have : Subsingleton J := Module.finrank_zero_iff.mp (Nat.le_zero.mp hN)
    exact ⟨emptyDecomposition⟩
  | succ N ih =>
    intro J _ _ _ _ hN
    classical
    cases subsingleton_or_nontrivial J with
    | inl h =>
      let := h
      exact ⟨emptyDecomposition⟩
    | inr h =>
      let := h
      obtain ⟨S, hS, hne, hmin⟩ := exists_minimal_ideal (J := J)
      obtain ⟨c, hc, hi, hu⟩ := ideal_unit hS
      have hEq := ideal_eq_peirceOneSub hS hc hi hu
      have hSI : Ideal (peirceOneSub hi) := hEq ▸ hS
      have hsimple : Simple ↥(peirceOneSub hi) := by
        apply minimal_ideal_simple hi hSI
        · rwa [← hEq]
        · simpa only [← hEq] using hmin
      have hc0 : c ≠ 0 := by
        intro hz
        apply hne
        apply (S.eq_bot_iff).mpr
        intro x hx
        have hu' := hu x hx
        rw [hz, zero_mul] at hu'
        exact hu'.symm
      have hdim : Module.finrank ℝ ↥(peirceZeroSub hi) ≤ N :=
        Nat.lt_succ_iff.mp (lt_of_lt_of_le (finrank_peirceZeroSub_lt hi hc0) hN)
      obtain ⟨D⟩ := ih ↥(peirceZeroSub hi) hdim
      exact ⟨prependDecomposition { V := ↥(peirceOneSub hi) } D hsimple
        (idealSplitEquiv hi hSI) (idealSplitEquiv_unit hi hSI) (idealSplitEquiv_mul hi hSI)⟩

/-- Every finite-dimensional Euclidean Jordan algebra is a finite product of simple ones. -/
theorem simple_decomposition [FiniteDimensional ℝ J] : Nonempty (Decomposition J) :=
  simple_decomposition_of_finrank_le (Module.finrank ℝ J) J le_rfl

end PaperA.Lib

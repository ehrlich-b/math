import PaperA.Definitions
import PaperA.PhysicsDefinitions

/-! A scalar model of the live effect-guarded interface. This certifies neither
historical releases nor the indebted statement scaffold. -/
noncomputable section

namespace PaperA.OperationalWitness

open EuclideanJordan

/-- The ordinary real product and inner product give a concrete EJA. -/
instance scalarEJA : EuclideanJordanAlgebra ℝ where
  mul := (· * ·)
  one := 1
  mul_comm := _root_.mul_comm
  add_mul := _root_.add_mul
  smul_mul := fun r x y => by simp only [smul_eq_mul]; ring
  one_mul := _root_.one_mul
  jordan := fun x y => by ring
  inner_assoc := fun x y z => by simp only [RCLike.inner_apply, conj_trivial]; ring

theorem positive_iff (a : ℝ) : PaperA.Positive a ↔ 0 ≤ a := by
  constructor
  · rintro ⟨x, rfl⟩
    exact mul_self_nonneg x
  · intro ha
    exact ⟨Real.sqrt a, Real.mul_self_sqrt ha⟩

theorem effect_iff (a : ℝ) : PaperA.IsEffect a ↔ 0 ≤ a ∧ a ≤ 1 := by
  simp only [PaperA.IsEffect, PaperA.Below, positive_iff, sub_nonneg]

theorem ouNorm_eq_abs (a : ℝ) : PaperA.ouNorm a = |a| := by
  have hs : {r : ℝ | 0 ≤ r ∧ PaperA.Below (-r • (1 : ℝ)) a ∧
      PaperA.Below a (r • (1 : ℝ))} = Set.Ici |a| := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, PaperA.Below, positive_iff,
      smul_eq_mul, mul_one]
    constructor
    · rintro ⟨_, hlo, hhi⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · intro h
      obtain ⟨hlo, hhi⟩ := abs_le.mp h
      exact ⟨(abs_nonneg a).trans h, by linarith, by linarith⟩
  unfold PaperA.ouNorm
  rw [hs, csInf_Ici]

/-- Multiplication satisfies every field, with the original order-unit S2. -/
def scalarProduct : PaperA.SequentialProduct ℝ where
  sp := (· * ·)
  closed := by
    intro a b ha hb
    obtain ⟨ha0, ha1⟩ := (effect_iff a).mp ha
    obtain ⟨hb0, hb1⟩ := (effect_iff b).mp hb
    exact (effect_iff _).mpr ⟨mul_nonneg ha0 hb0,
      (mul_le_mul_of_nonneg_right ha1 hb0).trans (by simpa using hb1)⟩
  S1 := by intros; exact mul_add _ _ _
  S2 := by
    intro b hb a _ ε hε
    obtain ⟨hb0, hb1⟩ := (effect_iff b).mp hb
    refine ⟨ε, hε, ?_⟩
    intro a' _ h
    rw [ouNorm_eq_abs] at h ⊢
    rw [← sub_mul, abs_mul, abs_of_nonneg hb0]
    exact (mul_le_mul_of_nonneg_left hb1 (abs_nonneg (a' - a))).trans_lt
      (by simpa using h)
  S3 := by intros; exact one_mul _
  S4 := by intro a b _ _ h; simpa only [mul_comm b a] using h
  S5 := by intros; exact (mul_assoc _ _ _).symm
  S6_compl := by intros; exact mul_comm _ _
  S6_sum := by intros; exact mul_comm _ _
  S7 := by intros; exact mul_comm _ _

theorem scalar_sp (a b : ℝ) : scalarProduct.sp a b = a * b := rfl

theorem zero_effect : PaperA.IsEffect (0 : ℝ) :=
  (effect_iff _).mpr ⟨le_rfl, zero_le_one⟩

theorem one_effect : PaperA.IsEffect (1 : ℝ) :=
  (effect_iff _).mpr ⟨zero_le_one, le_rfl⟩

theorem effect_equality (a b : ℝ) (ha : PaperA.IsEffect a) (hb : PaperA.IsEffect b) :
    ((⟨a, ha⟩ : PaperA.Effects ℝ) = ⟨b, hb⟩ ↔ a = b) := by
  constructor
  · exact congrArg Subtype.val
  · intro h
    exact Subtype.ext h

theorem distinct_effects : (⟨0, zero_effect⟩ : PaperA.Effects ℝ) ≠ ⟨1, one_effect⟩ := by
  intro h
  exact zero_ne_one (congrArg Subtype.val h)

end PaperA.OperationalWitness

import ObserverCapacity
import Mathlib.Tactic.NormNum

/-! Exact initial-memory witness: a uniform hidden bit is already in memory.
The fresh observation is constant. A matching action survives one step. -/
namespace ObserverCapacity
namespace InitialExamples
open scoped BigOperators NNReal
noncomputable section

/-- The initial hidden bit is copied to memory, with total weight one. -/
def hiddenBit : Bool → Bool → ℝ≥0 := fun x m => if x = m then 1 / 2 else 0

/-- The next state is alive exactly when the action guesses the hidden bit. -/
def guessing : Model Bool Unit Bool Bool where
  P x u z := if z = (x == u) then 1 else 0
  P_total x u := by cases x <;> cases u <;> norm_num [Fintype.sum_bool]
  C _ _ := 1
  C_total _ := by simp
  alive := id
  update m _ := m
  policy := id

lemma hiddenBit_marginal (x : Bool) : marginal hiddenBit x = 1 / 2 := by
  cases x <;> norm_num [marginal, hiddenBit, Fintype.sum_bool]

lemma hiddenBit_ML0 : ML0 hiddenBit = 2 := by
  norm_num [ML0, ML, initialChannel, hiddenBit_marginal, hiddenBit,
    Fintype.sum_bool, Fintype.univ_bool]

lemma guessing_capacity :
    min (min (ML guessing.C) (Fintype.card Bool : ℝ≥0)) (Fintype.card Bool : ℝ≥0) = 1 := by
  norm_num [ML, guessing, Fintype.univ_bool]

lemma hiddenBit_closed : jointClosed guessing 1 hiddenBit = 1 := by
  norm_num [jointClosed, closed, step, guessing, hiddenBit, Fintype.sum_bool]

lemma hiddenBit_blind : best guessing.P guessing.alive 1 (marginal hiddenBit) = 1 / 2 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro us _
    cases h : us 0 <;>
      norm_num [blind, step, guessing, hiddenBit_marginal, Fintype.sum_bool, h]
  · have h := blind_le_best guessing.P guessing.alive 1 (fun _ => false) (marginal hiddenBit)
    norm_num [blind, step, guessing, hiddenBit_marginal, Fintype.sum_bool] at h ⊢
    exact h

/-- The initial memory is correlated with the hidden state. -/
lemma hiddenBit_not_independent : hiddenBit false false ≠
    marginal hiddenBit false * (∑ x, hiddenBit x false) := by
  norm_num [hiddenBit_marginal, hiddenBit, Fintype.sum_bool]

/-- C-prime is attained with S=1, B=1/2, ML0=2 and fresh capacity=1. -/
theorem hidden_bit_equality :
    jointClosed guessing 1 hiddenBit = ML0 hiddenBit *
      min (min (ML guessing.C) (Fintype.card Bool : ℝ≥0)) (Fintype.card Bool : ℝ≥0) ^ 1 *
        best guessing.P guessing.alive 1 (marginal hiddenBit) := by
  rw [hiddenBit_closed, hiddenBit_ML0, guessing_capacity, hiddenBit_blind]
  norm_num

/-- Omitting the initial-information factor gives a strict false inequality. -/
theorem hidden_bit_violates_unqualified_fixed_memory :
    jointClosed guessing 1 hiddenBit >
      min (min (ML guessing.C) (Fintype.card Bool : ℝ≥0)) (Fintype.card Bool : ℝ≥0) ^ 1 *
        best guessing.P guessing.alive 1 (marginal hiddenBit) := by
  rw [hiddenBit_closed, guessing_capacity, hiddenBit_blind]
  norm_num

/-- The witness is explicitly an instance of the universal joint-law theorem. -/
theorem hidden_bit_instance :
    jointClosed guessing 1 hiddenBit ≤ ML0 hiddenBit *
      min (min (ML guessing.C) (Fintype.card Bool : ℝ≥0)) (Fintype.card Bool : ℝ≥0) ^ 1 *
        best guessing.P guessing.alive 1 (marginal hiddenBit) :=
  persistence_capacity_bound_initial guessing 1 hiddenBit

end
end InitialExamples
end ObserverCapacity

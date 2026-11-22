import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Persistence and finite observer capacity

At each step observe the current state, update the memory, take the action
specified by the updated memory, then sample the next state. Survival means
that every next state through the horizon belongs to `alive`. The original
bound has fixed initial memory independent of the initial state;
`persistence_capacity_bound_initial` extends it to arbitrary joint initial
weights with the factor `ML0`. Fresh observations have law `C` conditional on
the current state; there is no additional side channel.
All weights are nonnegative reals, so the finite sums are actual probabilities
when the initial distribution and transition/sensing rows have total mass one.
-/

namespace ObserverCapacity
open scoped BigOperators NNReal
noncomputable section

variable {X Y M U : Type*} [Fintype X] [Fintype Y] [Fintype M] [Fintype U]

/-- A stochastic finite controlled chain and a deterministic finite observer. -/
structure Model (X Y M U : Type*) [Fintype X] [Fintype Y] where
  P : X → U → X → ℝ≥0
  P_total : ∀ x u, ∑ x', P x u x' = 1
  C : X → Y → ℝ≥0
  C_total : ∀ x, ∑ y, C x y = 1
  alive : X → Bool
  update : M → Y → M
  policy : M → U

/-- Push forward a possibly unnormalized state distribution, killing dead arrivals. -/
def step (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (μ : X → ℝ≥0) (u : U) (x' : X) : ℝ≥0 :=
  ∑ x, μ x * P x u x' * (if alive x' then 1 else 0)

/-- Open-loop survival for a fixed word of `T` actions. -/
def blind (P : X → U → X → ℝ≥0) (alive : X → Bool) :
    (T : ℕ) → (Fin T → U) → (X → ℝ≥0) → ℝ≥0
  | 0, _, μ => ∑ x, μ x
  | T + 1, us, μ => blind P alive T (Fin.tail us) (step P alive μ (us 0))

/-- Best survival among all action words, chosen before the experiment. -/
def best (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (T : ℕ) (μ : X → ℝ≥0) : ℝ≥0 :=
  Finset.univ.sup fun us : Fin T → U => blind P alive T us μ

omit [Fintype U] in
lemma blind_mono (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (T : ℕ) (us : Fin T → U) {μ ν : X → ℝ≥0} (h : ∀ x, μ x ≤ ν x) :
    blind P alive T us μ ≤ blind P alive T us ν := by
  induction T generalizing μ ν with
  | zero => exact Finset.sum_le_sum fun x _ => h x
  | succ T ih =>
    change blind P alive T _ _ ≤ blind P alive T _ _
    apply ih
    intro x'
    exact Finset.sum_le_sum fun x _ => mul_le_mul_left (mul_le_mul_left (h x) _) _

omit [Fintype U] in
lemma blind_smul (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (T : ℕ) (us : Fin T → U) (r : ℝ≥0) (μ : X → ℝ≥0) :
    blind P alive T us (fun x => r * μ x) = r * blind P alive T us μ := by
  induction T generalizing μ with
  | zero => exact (Finset.mul_sum ..).symm
  | succ T ih =>
    have hs : step P alive (fun x => r * μ x) (us 0) =
        fun x' => r * step P alive μ (us 0) x' := by
      funext x'
      simp only [step, Finset.mul_sum, mul_assoc]
    simpa only [blind, hs] using ih (Fin.tail us) (step P alive μ (us 0))

lemma blind_le_best (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (T : ℕ) (us : Fin T → U) (μ : X → ℝ≥0) :
    blind P alive T us μ ≤ best P alive T μ :=
  show blind P alive T us μ ≤ Finset.univ.sup (fun us => blind P alive T us μ) from
    Finset.le_sup (f := fun us => blind P alive T us μ) (Finset.mem_univ us)

lemma best_mono (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (T : ℕ) {μ ν : X → ℝ≥0} (h : ∀ x, μ x ≤ ν x) :
    best P alive T μ ≤ best P alive T ν := by
  apply Finset.sup_le
  intro us _
  exact (blind_mono P alive T us h).trans (blind_le_best P alive T us ν)

lemma best_smul_le (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (T : ℕ) (r : ℝ≥0) (μ : X → ℝ≥0) :
    best P alive T (fun x => r * μ x) ≤ r * best P alive T μ := by
  apply Finset.sup_le
  intro us _
  rw [blind_smul]
  exact mul_le_mul_right (blind_le_best P alive T us μ) r

lemma best_step_le (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (T : ℕ) (μ : X → ℝ≥0) (u : U) :
    best P alive T (step P alive μ u) ≤ best P alive (T + 1) μ := by
  apply Finset.sup_le
  intro us _
  simpa [blind] using blind_le_best P alive (T + 1) (Fin.cons u us) μ

/-- General observer with an input channel that may also depend on prior memory. -/
def closed (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (H : M → X → Y → ℝ≥0) (g : M → Y → M) (π : M → U) :
    ℕ → (X → ℝ≥0) → M → ℝ≥0
  | 0, μ, _ => ∑ x, μ x
  | T + 1, μ, m => ∑ y,
      closed P alive H g π T
        (step P alive (fun x => μ x * H m x y) (π (g m y))) (g m y)

omit [Fintype M] in
/-- Columnwise domination turns feedback into a mixture of open-loop words. -/
theorem closed_le_envelope [Nonempty U]
    (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (H : M → X → Y → ℝ≥0) (g : M → Y → M) (π : M → U)
    (r : Y → ℝ≥0) (hr : ∀ m x y, H m x y ≤ r y)
    (T : ℕ) (μ : X → ℝ≥0) (m : M) :
    closed P alive H g π T μ m ≤ (∑ y, r y) ^ T * best P alive T μ := by
  induction T generalizing μ m with
  | zero =>
    simp [closed, best, blind]
  | succ T ih =>
    simp only [closed]
    calc
      _ ≤ ∑ y, (∑ z, r z) ^ T *
          best P alive T (step P alive (fun x => μ x * H m x y) (π (g m y))) :=
        Finset.sum_le_sum fun y _ => ih _ _
      _ ≤ ∑ y, (∑ z, r z) ^ T * (r y * best P alive (T + 1) μ) := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_right
        calc
          _ ≤ best P alive T (fun x' => r y * step P alive μ (π (g m y)) x') := by
            apply best_mono
            intro x'
            simp only [step, Finset.mul_sum]
            apply Finset.sum_le_sum
            intro x _
            calc
              _ ≤ (μ x * r y) * P x (π (g m y)) x' *
                  (if alive x' then 1 else 0) := by gcongr; exact hr m x y
              _ = _ := by ring
          _ ≤ r y * best P alive T (step P alive μ (π (g m y))) :=
            best_smul_le ..
          _ ≤ r y * best P alive (T + 1) μ := mul_le_mul_right (best_step_le ..) _
      _ = _ := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, pow_succ]
        ring

/-- Statewise survival, equivalent to the unnormalized distribution recursion. -/
def value (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (H : M → X → Y → ℝ≥0) (g : M → Y → M) (π : M → U) :
    ℕ → X → M → ℝ≥0
  | 0, _, _ => 1
  | T + 1, x, m => ∑ y, H m x y * ∑ x',
      P x (π (g m y)) x' * (if alive x' then 1 else 0) * value P alive H g π T x' (g m y)

omit [Fintype M] [Fintype U] in
lemma closed_eq_value (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (H : M → X → Y → ℝ≥0) (g : M → Y → M) (π : M → U)
    (T : ℕ) (μ : X → ℝ≥0) (m : M) :
    closed P alive H g π T μ m = ∑ x, μ x * value P alive H g π T x m := by
  induction T generalizing μ m with
  | zero => simp [closed, value]
  | succ T ih =>
    simp only [closed, value, ih, step, Finset.sum_mul, Finset.mul_sum]
    calc
      _ = ∑ y, ∑ x, ∑ x', μ x * H m x y * P x (π (g m y)) x' *
          (if alive x' then 1 else 0) * value P alive H g π T x' (g m y) := by
        apply Finset.sum_congr rfl
        intro y _
        exact Finset.sum_comm
      _ = ∑ x, ∑ y, ∑ x', μ x * H m x y * P x (π (g m y)) x' *
          (if alive x' then 1 else 0) * value P alive H g π T x' (g m y) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro x' _
        ring

/-- The actual information-bearing observation channel collapsed to next memory. -/
def memoryChannel (C : X → Y → ℝ≥0) (g : M → Y → M)
    (m : M) (x : X) (m' : M) : ℝ≥0 := by
  classical
  exact ∑ y, if g m y = m' then C x y else 0

omit [Fintype M] [Fintype U] in
lemma memoryChannel_le_one (d : Model X Y M U) (m : M) (x : X) (m' : M) :
    memoryChannel d.C d.update m x m' ≤ 1 := by
  classical
  calc
    _ ≤ ∑ y, d.C x y := Finset.sum_le_sum fun y _ => by split_ifs <;> simp
    _ = 1 := d.C_total x

omit [Fintype U] in
lemma value_memory (d : Model X Y M U) (T : ℕ) (x : X) (m : M) :
    value d.P d.alive (fun _ => d.C) d.update d.policy T x m =
      value d.P d.alive (memoryChannel d.C d.update) (fun _ m' => m') d.policy T x m := by
  classical
  induction T generalizing x m with
  | zero => rfl
  | succ T ih =>
    simp only [value, ih, memoryChannel, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_eq_single (d.update m y)]
    · simp
    · intro m' _ h
      simp [Ne.symm h]
    · simp

omit [Fintype U] in
lemma closed_memory (d : Model X Y M U) (T : ℕ) (μ : X → ℝ≥0) (m : M) :
    closed d.P d.alive (fun _ => d.C) d.update d.policy T μ m =
      closed d.P d.alive (memoryChannel d.C d.update) (fun _ m' => m') d.policy T μ m := by
  simp only [closed_eq_value, value_memory]

/-- Statewise survival under a predetermined action word. -/
def openValue (P : X → U → X → ℝ≥0) (alive : X → Bool) :
    (T : ℕ) → (Fin T → U) → X → ℝ≥0
  | 0, _, _ => 1
  | T + 1, us, x => ∑ x', P x (us 0) x' *
      (if alive x' then 1 else 0) * openValue P alive T (Fin.tail us) x'

omit [Fintype U] in
lemma blind_eq_value (P : X → U → X → ℝ≥0) (alive : X → Bool)
    (T : ℕ) (us : Fin T → U) (μ : X → ℝ≥0) :
    blind P alive T us μ = ∑ x, μ x * openValue P alive T us x := by
  induction T generalizing μ with
  | zero => simp [blind, openValue]
  | succ T ih =>
    simp only [blind, openValue, ih, step, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro x' _
    ring

/-- The sum of survival probabilities for all open-loop words (a union bound). -/
def cover (P : X → U → X → ℝ≥0) (alive : X → Bool) (T : ℕ) (x : X) : ℝ≥0 :=
  ∑ us : Fin T → U, openValue P alive T us x

lemma cover_succ (P : X → U → X → ℝ≥0) (alive : X → Bool) (T : ℕ) (x : X) :
    cover P alive (T + 1) x = ∑ u, ∑ x',
      P x u x' * (if alive x' then 1 else 0) * cover P alive T x' := by
  classical
  unfold cover
  rw [← (Fin.consEquiv (fun _ : Fin (T + 1) => U)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, openValue,
    Fin.cons_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact Finset.sum_comm

omit [Fintype M] in
lemma value_le_cover (d : Model X Y M U) (T : ℕ) (x : X) (m : M) :
    value d.P d.alive (fun _ => d.C) d.update d.policy T x m ≤
      cover d.P d.alive T x := by
  classical
  induction T generalizing x m with
  | zero => simp [value, cover, openValue]
  | succ T ih =>
    rw [value, cover_succ]
    calc
      _ ≤ ∑ y, d.C x y * ∑ x', d.P x (d.policy (d.update m y)) x' *
          (if d.alive x' then 1 else 0) * cover d.P d.alive T x' := by
        apply Finset.sum_le_sum
        intro y _
        gcongr with x'
        exact ih x' (d.update m y)
      _ ≤ ∑ y, d.C x y * (∑ u, ∑ x', d.P x u x' *
          (if d.alive x' then 1 else 0) * cover d.P d.alive T x') := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_right
        exact Finset.single_le_sum
          (f := fun u : U => ∑ x', d.P x u x' *
            (if d.alive x' then 1 else 0) * cover d.P d.alive T x')
          (fun _ _ => zero_le) (Finset.mem_univ (d.policy (d.update m y)))
      _ = _ := by rw [← Finset.sum_mul, d.C_total, one_mul]

/-- Maximal leakage in its multiplicative convention (not its logarithm). -/
def ML (C : X → Y → ℝ≥0) : ℝ≥0 := ∑ y, Finset.univ.sup fun x => C x y

/-- All three capacity bounds, before taking their minimum. -/
theorem three_bounds [Nonempty U] (d : Model X Y M U)
    (T : ℕ) (μ : X → ℝ≥0) (m : M) :
    let S := closed d.P d.alive (fun _ => d.C) d.update d.policy T μ m
    let B := best d.P d.alive T μ
    S ≤ ML d.C ^ T * B ∧
      S ≤ (Fintype.card M : ℝ≥0) ^ T * B ∧
      S ≤ (Fintype.card U : ℝ≥0) ^ T * B := by
  classical
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · exact closed_le_envelope d.P d.alive (fun _ => d.C) d.update d.policy
      (fun y => Finset.univ.sup fun x => d.C x y)
      (fun _ x y => Finset.le_sup (f := fun x => d.C x y) (Finset.mem_univ x)) T μ m
  · rw [closed_memory]
    simpa using closed_le_envelope d.P d.alive (memoryChannel d.C d.update)
      (fun _ m' => m') d.policy (fun _ => 1)
      (fun m x m' => memoryChannel_le_one d m x m') T μ m
  · calc
      _ ≤ ∑ x, μ x * cover d.P d.alive T x := by
        rw [closed_eq_value]
        exact Finset.sum_le_sum fun x _ => mul_le_mul_right (value_le_cover d T x m) (μ x)
      _ = ∑ us : Fin T → U, blind d.P d.alive T us μ := by
        simp only [cover, Finset.mul_sum, blind_eq_value]
        exact Finset.sum_comm
      _ ≤ ∑ _us : Fin T → U, best d.P d.alive T μ :=
        Finset.sum_le_sum fun us _ => blind_le_best d.P d.alive T us μ
      _ = _ := by simp [Nat.cast_pow]

/-- The persistence capacity bound, for arbitrary finite chains and horizons.

The conclusion holds even for unnormalized nonnegative initial weights. For
`∑ x, μ x = 1`, `closed` is precisely the probability of `x₁,...,x_T ∈ alive`
and `best` is the best open-loop probability for the same initial law.
-/
theorem persistence_capacity_bound [Nonempty U] (d : Model X Y M U)
    (T : ℕ) (μ : X → ℝ≥0) (m : M) :
    closed d.P d.alive (fun _ => d.C) d.update d.policy T μ m ≤
      min (min (ML d.C) (Fintype.card M : ℝ≥0)) (Fintype.card U : ℝ≥0) ^ T *
        best d.P d.alive T μ := by
  obtain ⟨hC, hM, hU⟩ := three_bounds d T μ m
  simp only [min_def]
  split_ifs <;> first | exact hC | exact hM | exact hU

/-- State marginal of an arbitrary, possibly unnormalized joint initial weight. -/
def marginal (ν : X → M → ℝ≥0) (x : X) : ℝ≥0 := ∑ m, ν x m

/-- Initial memory channel; zero-marginal states have a zero row. -/
def initialChannel (ν : X → M → ℝ≥0) (x : X) (m : M) : ℝ≥0 :=
  ν x m / marginal ν x

/-- Multiplicative initial maximal leakage, restricted to the marginal support. -/
def ML0 (ν : X → M → ℝ≥0) : ℝ≥0 := ML (initialChannel ν)

/-- Closed survival integrated against the actual joint initial weight. -/
def jointClosed (d : Model X Y M U) (T : ℕ) (ν : X → M → ℝ≥0) : ℝ≥0 :=
  ∑ m, closed d.P d.alive (fun _ => d.C) d.update d.policy T (fun x => ν x m) m

lemma joint_le_column (ν : X → M → ℝ≥0) (x : X) (m : M) :
    ν x m ≤ (Finset.univ.sup fun z => initialChannel ν z m) * marginal ν x := by
  classical
  have hle : ν x m ≤ marginal ν x :=
    Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ m)
  by_cases h : marginal ν x = 0
  · simpa [h] using hle
  · calc
      ν x m = initialChannel ν x m * marginal ν x := by
        simp [initialChannel, div_mul_cancel₀ _ h]
      _ ≤ _ := mul_le_mul_left
        (Finset.le_sup (f := fun z => initialChannel ν z m) (Finset.mem_univ x)) _

/-- Theorem C-prime: arbitrary joint initial information costs a factor ML0.

No normalization or independence hypothesis is imposed on ν. Null marginal
states contribute zero to the initial channel, including the all-zero law.
-/
theorem persistence_capacity_bound_initial [Nonempty U] (d : Model X Y M U)
    (T : ℕ) (ν : X → M → ℝ≥0) :
    jointClosed d T ν ≤ ML0 ν *
      min (min (ML d.C) (Fintype.card M : ℝ≥0)) (Fintype.card U : ℝ≥0) ^ T *
        best d.P d.alive T (marginal ν) := by
  classical
  let K := min (min (ML d.C) (Fintype.card M : ℝ≥0)) (Fintype.card U : ℝ≥0) ^ T
  calc
    jointClosed d T ν ≤ ∑ m, K * best d.P d.alive T (fun x => ν x m) :=
      Finset.sum_le_sum fun m _ => persistence_capacity_bound d T (fun x => ν x m) m
    _ ≤ ∑ m, K * ((Finset.univ.sup fun x => initialChannel ν x m) *
        best d.P d.alive T (marginal ν)) := by
      apply Finset.sum_le_sum
      intro m _
      apply mul_le_mul_right
      exact (best_mono d.P d.alive T (fun x => joint_le_column ν x m)).trans
        (best_smul_le d.P d.alive T _ (marginal ν))
    _ = _ := by
      dsimp [K]
      simp only [← Finset.mul_sum, ← Finset.sum_mul, ML0, ML]
      ring

end
end ObserverCapacity

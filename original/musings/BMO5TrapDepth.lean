import Mathlib.Data.Nat.Prime.Pow
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# BMO 5 threshold traps

Kernel-checked arithmetic behind the two nested families of fixed-level
stopping prehistories in the shifted BMO 5 recurrence. Background: the
bbchallenge community, *Beaver Math Olympiad*, Problem 5. The underlying
machine was found by mxdys in 2024. DOI: unknown.
-/

namespace BMO5

/-- The stopping coordinate at threshold level `a`. -/
def target (a : ℕ) : ℕ := 20 * 2 ^ a + a + 1

/-- The period used for roots modulo `3^k`, with parity retained. -/
def period (k : ℕ) : ℕ := 2 * 3 ^ k

theorem period_pos (k : ℕ) : 0 < period k := by
  simp [period]

theorem period_succ (k : ℕ) : period (k + 1) = 3 * period k := by
  simp [period, pow_succ]
  ring

theorem four_pow_three_pow_eq (k : ℕ) :
    ∃ w : ℕ, 4 ^ (3 ^ k) = 1 + 3 ^ (k + 1) * w := by
  induction k with
  | zero =>
      exact ⟨1, by norm_num⟩
  | succ k ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨w + 3 * 3 ^ k * w ^ 2 + 3 * (3 ^ k) ^ 2 * w ^ 3, ?_⟩
      calc
        4 ^ (3 ^ (k + 1)) = (4 ^ (3 ^ k)) ^ 3 := by
          rw [pow_succ, pow_mul]
        _ = (1 + 3 ^ (k + 1) * w) ^ 3 := by rw [hw]
        _ = 1 + 3 ^ (k + 2) *
              (w + 3 * 3 ^ k * w ^ 2 + 3 * (3 ^ k) ^ 2 * w ^ 3) := by
          rw [show 3 ^ (k + 1) = 3 ^ k * 3 by rw [pow_succ],
            show 3 ^ (k + 2) = 3 ^ k * 3 * 3 by
              rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, pow_succ]]
          ring

theorem four_pow_three_pow_modEq (k : ℕ) :
    Nat.ModEq (3 ^ (k + 1)) (4 ^ (3 ^ k)) 1 := by
  obtain ⟨w, hw⟩ := four_pow_three_pow_eq k
  rw [hw]
  simp [Nat.ModEq, Nat.add_mod]

theorem four_pow_mul_three_pow_modEq (k t : ℕ) :
    Nat.ModEq (3 ^ (k + 1)) (4 ^ (t * 3 ^ k)) 1 := by
  rw [mul_comm, pow_mul]
  simpa using (four_pow_three_pow_modEq k).pow t

/-- Moving by `2 * t * 3^k` changes the target by only the linear term,
modulo `3^(k+1)`. -/
theorem target_shift_modEq (k r t : ℕ) :
    Nat.ModEq (3 ^ (k + 1))
      (target (r + 2 * t * 3 ^ k))
      (target r + 2 * t * 3 ^ k) := by
  have hpow : Nat.ModEq (3 ^ (k + 1)) (2 ^ (2 * t * 3 ^ k)) 1 := by
    convert four_pow_mul_three_pow_modEq k t using 1
    · rw [show 2 * t * 3 ^ k = 2 * (t * 3 ^ k) by ring, pow_mul]
      norm_num
  unfold target
  rw [pow_add]
  have h := (hpow.mul_left (20 * 2 ^ r)).add
    (Nat.ModEq.refl (r + 2 * t * 3 ^ k + 1))
  convert h using 1 <;> ring

theorem unique_ternary_lift_digit (u : ℕ) :
    ∃! t : ℕ, t < 3 ∧ 3 ∣ u + 2 * t := by
  let d := u % 3
  refine ⟨d, ?_, ?_⟩
  · constructor
    · exact Nat.mod_lt _ (by norm_num)
    · use u / 3 + d
      have hu := Nat.div_add_mod u 3
      dsimp [d]
      omega
  · intro t ht
    obtain ⟨z, hz⟩ := ht.2
    have hu := Nat.div_add_mod u 3
    have hd : d < 3 := Nat.mod_lt _ (by norm_num)
    dsimp [d] at hu hd ⊢
    omega

/-- A depth-`k` root has exactly one parity-preserving lift among its three
representatives at depth `k+1`. -/
theorem existsUnique_root_lift (k r : ℕ) (hr : 3 ^ k ∣ target r) :
    ∃! t : ℕ, t < 3 ∧ 3 ^ (k + 1) ∣ target (r + 2 * t * 3 ^ k) := by
  obtain ⟨t, ht, htu⟩ := unique_ternary_lift_digit (target r / 3 ^ k)
  refine ⟨t, ?_, ?_⟩
  · refine ⟨ht.1, ?_⟩
    have hshift := target_shift_modEq k r t
    rw [← Nat.modEq_zero_iff_dvd]
    apply hshift.trans
    rw [Nat.modEq_zero_iff_dvd]
    rw [show target r = 3 ^ k * (target r / 3 ^ k) by
      exact (Nat.mul_div_cancel' hr).symm]
    rw [show k + 1 = k + 1 by rfl, pow_succ]
    have : 3 ∣ target r / 3 ^ k + 2 * t := ht.2
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using
      (Nat.mul_dvd_mul_left (3 ^ k) this)
  · intro t' ht'
    apply htu
    refine ⟨ht'.1, ?_⟩
    have hshift := target_shift_modEq k r t'
    have hright : 3 ^ (k + 1) ∣ target r + 2 * t' * 3 ^ k :=
      (hshift.dvd_iff (dvd_refl _)).mp ht'.2
    rw [show target r = 3 ^ k * (target r / 3 ^ k) by
      exact (Nat.mul_div_cancel' hr).symm] at hright
    rw [pow_succ] at hright
    have : 3 ^ k * 3 ∣ 3 ^ k * (target r / 3 ^ k + 2 * t') := by
      convert hright using 1
      all_goals ring
    exact (mul_dvd_mul_iff_left (by positivity : 3 ^ k ≠ 0)).mp this

/-- In a complete parity-retaining period, a root is unique within each
parity. This is the exact two-class theorem, expressed without choosing
noncanonical representatives. -/
theorem existsUnique_root_of_parity (k p : ℕ) (hp : p < 2) :
    ∃! r : ℕ,
      r < period (k + 1) ∧ r % 2 = p ∧ 3 ^ (k + 1) ∣ target r := by
  induction k with
  | zero =>
      interval_cases p
      · refine ⟨0, by norm_num [period, target], ?_⟩
        intro r hr
        rcases hr with ⟨hrlt, hrparity, hrroot⟩
        norm_num [period] at hrlt
        interval_cases r <;> norm_num [target] at hrroot
        all_goals norm_num at hrparity
        all_goals rfl
      · refine ⟨1, by norm_num [period, target], ?_⟩
        intro r hr
        rcases hr with ⟨hrlt, hrparity, hrroot⟩
        norm_num [period] at hrlt
        interval_cases r <;> norm_num [target] at hrroot
        all_goals norm_num at hrparity
        all_goals rfl
  | succ k ih =>
      let d := k + 1
      obtain ⟨r, hr, hrunique⟩ := ih
      obtain ⟨t, ht, htunique⟩ := existsUnique_root_lift d r hr.2.2
      let x := r + 2 * t * 3 ^ d
      refine ⟨x, ?_, ?_⟩
      · have hperiod : period (d + 1) = 3 * period d := period_succ d
        have hxform : x = r + period d * t := by simp [x, period]; ring
        have ht' : t ≤ 2 := by omega
        have hmul : period d * t ≤ period d * 2 := Nat.mul_le_mul_left _ ht'
        have hrlt : r < period d := by simpa [d] using hr.1
        refine ⟨?_, ?_, ht.2⟩
        · rw [hperiod, hxform]
          omega
        · dsimp [x]
          simpa [Nat.add_mod, Nat.mul_mod] using hr.2.1
      · intro y hy
        let y₀ := y % period d
        let q := y / period d
        have hdecomp : y₀ + period d * q = y := by
          simpa [y₀, q] using Nat.mod_add_div y (period d)
        have hq : q < 3 := by
          apply (Nat.div_lt_iff_lt_mul (period_pos d)).2
          rw [← period_succ d]
          exact hy.1
        have hy₀lt : y₀ < period d := Nat.mod_lt _ (period_pos d)
        have htwo : 2 ∣ period d := by
          exact ⟨3 ^ d, by simp [period]⟩
        have hy₀parity : y₀ % 2 = p := by
          have hm : Nat.ModEq 2 y₀ y :=
            (Nat.mod_modEq y (period d)).of_dvd htwo
          change y₀ % 2 = y % 2 at hm
          exact hm.trans hy.2.1
        have harg : y₀ + 2 * q * 3 ^ d = y := by
          rw [← hdecomp]
          simp [period]
          ring
        have hshift := target_shift_modEq d y₀ q
        rw [harg] at hshift
        have hsum : 3 ^ (d + 1) ∣ target y₀ + 2 * q * 3 ^ d :=
          (hshift.dvd_iff (dvd_refl _)).mp hy.2.2
        have hsum' : 3 ^ d ∣ target y₀ + 2 * q * 3 ^ d :=
          (pow_dvd_pow 3 (Nat.le_succ d)).trans hsum
        have hterm : 3 ^ d ∣ 2 * q * 3 ^ d := by
          use 2 * q
          ring
        have hcancel : Nat.ModEq (3 ^ d)
            (target y₀ + 2 * q * 3 ^ d) (target y₀) := by
          convert (Nat.ModEq.refl (target y₀)).add hterm.modEq_zero_nat using 1
          simp
        have hy₀root : 3 ^ d ∣ target y₀ :=
          (hcancel.dvd_iff (dvd_refl _)).mp hsum'
        have hy₀eq : y₀ = r := hrunique y₀ ⟨hy₀lt, hy₀parity, hy₀root⟩
        have hynext : 3 ^ (d + 1) ∣ target y := by
          simpa [d] using hy.2.2
        rw [← harg] at hynext
        have hqroot : 3 ^ (d + 1) ∣ target (r + 2 * q * 3 ^ d) := by
          simpa [hy₀eq] using hynext
        have hqeq : q = t := htunique q ⟨hq, hqroot⟩
        dsimp [x]
        rw [← harg, hy₀eq, hqeq]

/-- Therefore every positive depth has exactly two roots in a complete
period: the unique even root and the unique odd root. -/
theorem exactly_two_root_classes (k : ℕ) :
    (∃! r : ℕ,
      r < period (k + 1) ∧ r % 2 = 0 ∧ 3 ^ (k + 1) ∣ target r) ∧
    (∃! r : ℕ,
      r < period (k + 1) ∧ r % 2 = 1 ∧ 3 ^ (k + 1) ∣ target r) := by
  exact ⟨existsUnique_root_of_parity k 0 (by omega),
    existsUnique_root_of_parity k 1 (by omega)⟩

/-- Root representatives in the standard complete period. -/
def roots (k : ℕ) : Finset ℕ :=
  (Finset.range (period k)).filter fun r => 3 ^ k ∣ target r

/-- The literal finite root count corresponding to `exactly_two_root_classes`. -/
theorem roots_card (k : ℕ) : (roots (k + 1)).card = 2 := by
  obtain ⟨re, hre, hreunique⟩ := existsUnique_root_of_parity k 0 (by omega)
  obtain ⟨ro, hro, hrounique⟩ := existsUnique_root_of_parity k 1 (by omega)
  apply Finset.card_eq_two.mpr
  refine ⟨re, ro, ?_, ?_⟩
  · intro h
    have hp := congrArg (fun n : ℕ => n % 2) h
    omega
  · ext x
    simp only [roots, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      have hp : x % 2 < 2 := Nat.mod_lt _ (by omega)
      interval_cases hxp : x % 2
      · exact Or.inl (hreunique x ⟨hx.1, hxp, hx.2⟩)
      · exact Or.inr (hrounique x ⟨hx.1, hxp, hx.2⟩)
    · rintro (rfl | rfl)
      · exact ⟨hre.1, hre.2.2⟩
      · exact ⟨hro.1, hro.2.2⟩

/-! ## Exact bridge to the shifted BMO 5 recurrence -/

/-- The threshold in the shifted two-variable recurrence. -/
def threshold (a : ℕ) : ℕ := 10 * 2 ^ a - 1

/-- The multiplicative coordinate for a state `(a,b)`. -/
def coord (a b : ℕ) : ℕ := 2 * b + a + 5

/-- The low-branch update of the second coordinate. -/
def lowNext (a b : ℕ) : ℕ := 3 * b + a + 5

theorem threshold_ge_two (a : ℕ) : 2 ≤ threshold a := by
  have hp : 1 ≤ 2 ^ a := one_le_pow₀ (by omega)
  simp [threshold]
  omega

theorem low_guard_iff (a b : ℕ) :
    b ≤ threshold a - 2 ↔ coord a b ≤ target a - 2 := by
  have hp : 1 ≤ 2 ^ a := one_le_pow₀ (by omega)
  simp [threshold, coord, target]
  omega

theorem halt_guard_iff (a b : ℕ) :
    b = threshold a - 1 ↔ coord a b = target a := by
  have hp : 1 ≤ 2 ^ a := one_le_pow₀ (by omega)
  simp [threshold, coord, target]
  omega

theorem high_guard_iff (a b : ℕ) :
    threshold a ≤ b ↔ target a + 2 ≤ coord a b := by
  have hp : 1 ≤ 2 ^ a := one_le_pow₀ (by omega)
  simp [threshold, coord, target]
  omega

theorem coord_lowNext (a b : ℕ) :
    coord a (lowNext a b) = 3 * coord a b := by
  simp [coord, lowNext]
  ring

theorem coord_highNext (a b : ℕ) (hb : threshold a ≤ b) :
    coord (a + 1) (b - threshold a) = coord a b - 20 * 2 ^ a + 3 := by
  have hp : 1 ≤ 2 ^ a := one_le_pow₀ (by omega)
  simp [threshold, coord] at hb ⊢
  omega

/-- A valid local stopping prehistory: every earlier coordinate is in the
low guard and the `t`-th coordinate is exactly the stopping target. -/
def ValidStoppingPrehistory (a t b : ℕ) : Prop :=
  (∀ j < t, 3 ^ j * coord a b ≤ target a - 2) ∧
    3 ^ t * coord a b = target a

/-- The same prehistory stated directly in the recurrence's second coordinate. -/
def StopsAfterLowSteps (a t b : ℕ) : Prop :=
  (∀ j < t, (lowNext a)^[j] b ≤ threshold a - 2) ∧
    (lowNext a)^[t] b = threshold a - 1

theorem coord_lowIterate (a b j : ℕ) :
    coord a ((lowNext a)^[j] b) = 3 ^ j * coord a b := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', coord_lowNext, ih, pow_succ]
      ring

theorem validStoppingPrehistory_iff_stopsAfterLowSteps (a t b : ℕ) :
    ValidStoppingPrehistory a t b ↔ StopsAfterLowSteps a t b := by
  constructor
  · rintro ⟨hlow, hhalt⟩
    refine ⟨?_, ?_⟩
    · intro j hj
      apply (low_guard_iff a _).mpr
      rw [coord_lowIterate]
      exact hlow j hj
    · apply (halt_guard_iff a _).mpr
      rw [coord_lowIterate]
      exact hhalt
  · rintro ⟨hlow, hhalt⟩
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [← coord_lowIterate]
      exact (low_guard_iff a _).mp (hlow j hj)
    · rw [← coord_lowIterate]
      exact (halt_guard_iff a _).mp hhalt

theorem target_parity (a : ℕ) : target a % 2 = (a + 1) % 2 := by
  simp [target, Nat.add_mod, Nat.mul_mod]

theorem three_pow_mod_two (n : ℕ) : 3 ^ n % 2 = 1 := by
  have h : Nat.ModEq 2 3 1 := by norm_num
  have hp := h.pow n
  change 3 ^ n % 2 = 1 ^ n % 2 at hp
  simpa using hp

/-- Every sufficiently large algebraic predecessor is an actual nonnegative
state, and its whole fixed-level path respects the low guard. -/
theorem validStoppingPrehistory_of_dvd_of_large (a t : ℕ)
    (hdiv : 3 ^ t ∣ target a)
    (hlarge : a + 5 ≤ target a / 3 ^ t) :
    ∃ b : ℕ, ValidStoppingPrehistory a t b := by
  let q := target a / 3 ^ t
  have hfactor : target a = 3 ^ t * q := by
    exact (Nat.mul_div_cancel' hdiv).symm
  have hqparity : q % 2 = (a + 1) % 2 := by
    have hp := congrArg (fun n : ℕ => n % 2) hfactor
    rw [target_parity] at hp
    simpa [Nat.mul_mod, three_pow_mod_two] using hp.symm
  let b := (q - (a + 5)) / 2
  have hcoord : coord a b = q := by
    dsimp [b, coord]
    omega
  refine ⟨b, ?_, ?_⟩
  · intro j hj
    have hqpos : 0 < q := by omega
    have hpow : 3 ^ j < 3 ^ t := by
      exact pow_lt_pow_right₀ (by omega : (1 : ℕ) < 3) hj
    have hlt : 3 ^ j * q < target a := by
      rw [hfactor]
      exact Nat.mul_lt_mul_of_pos_right hpow hqpos
    have hparity : (3 ^ j * q) % 2 = target a % 2 := by
      rw [hfactor]
      simp [Nat.mul_mod, three_pow_mod_two]
    rw [hcoord]
    omega
  · rw [hcoord, ← hfactor]

theorem sq_le_two_pow_of_four_le (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => norm_num
  | succ m ih =>
      calc
        (4 + (m + 1)) ^ 2 = ((4 + m) + 1) ^ 2 := by ring
        _ ≤ 2 * (4 + m) ^ 2 := by
          simp only [pow_two]
          nlinarith
        _ ≤ 2 * 2 ^ (4 + m) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (4 + (m + 1)) := by
          rw [show 4 + (m + 1) = (4 + m) + 1 by omega, pow_succ]
          ring

/-- Valid stopping prehistories have no uniform depth bound. This is a local
statement over all states, not a claim about the distinguished initial orbit. -/
theorem exists_validStoppingPrehistory (t : ℕ) :
    ∃ a b : ℕ, ValidStoppingPrehistory a t b := by
  cases t with
  | zero =>
      exact ⟨0, 8, by norm_num [ValidStoppingPrehistory, coord, target]⟩
  | succ k =>
      let d := k + 1
      obtain ⟨r, hr, _⟩ := existsUnique_root_of_parity k 0 (by omega)
      let a := r + period d
      have hshift := target_shift_modEq d r 1
      have hshift' := hshift.of_dvd (pow_dvd_pow 3 (Nat.le_succ d))
      have hperiodDiv : 3 ^ d ∣ 2 * 1 * 3 ^ d := by
        use 2
        ring
      have hsum : 3 ^ d ∣ target r + 2 * 1 * 3 ^ d :=
        dvd_add hr.2.2 hperiodDiv
      have hrootRaw : 3 ^ d ∣ target (r + 2 * 1 * 3 ^ d) :=
        (hshift'.dvd_iff (dvd_refl _)).mpr hsum
      have hroot : 3 ^ d ∣ target a := by
        simpa [a, period] using hrootRaw
      have hpow3 : 3 ≤ 3 ^ d := by
        have hone : 1 ≤ 3 ^ k := one_le_pow₀ (by omega)
        simp [d, pow_succ]
        omega
      have hperiodLe : period d ≤ a := by
        dsimp [a]
        omega
      have hthreeLe : 3 ^ d ≤ a := by
        have : 3 ^ d ≤ period d := by simp [period]
        exact this.trans hperiodLe
      have ha6 : 6 ≤ a := by
        have : 6 ≤ period d := by
          simp [period]
          omega
        exact this.trans hperiodLe
      have hsquare : a ^ 2 ≤ 2 ^ a :=
        sq_le_two_pow_of_four_le a (by omega)
      have hlargeMul : (a + 5) * 3 ^ d ≤ target a := by
        calc
          (a + 5) * 3 ^ d = 3 ^ d * (a + 5) := by ring
          _ ≤ a * (2 * a) := Nat.mul_le_mul hthreeLe (by omega)
          _ = 2 * a ^ 2 := by ring
          _ ≤ 2 * 2 ^ a := Nat.mul_le_mul_left 2 hsquare
          _ ≤ 20 * 2 ^ a := by omega
          _ ≤ target a := by simp [target]; omega
      have hlarge : a + 5 ≤ target a / 3 ^ d :=
        (Nat.le_div_iff_mul_le (by positivity)).2 hlargeMul
      obtain ⟨b, hb⟩ := validStoppingPrehistory_of_dvd_of_large a d hroot hlarge
      exact ⟨a, b, by simpa [d] using hb⟩

/-- Direct recurrence form of the unbounded-depth result. -/
theorem exists_stopsAfterLowSteps (t : ℕ) :
    ∃ a b : ℕ, StopsAfterLowSteps a t b := by
  obtain ⟨a, b, hab⟩ := exists_validStoppingPrehistory t
  exact ⟨a, b, (validStoppingPrehistory_iff_stopsAfterLowSteps a t b).mp hab⟩

end BMO5

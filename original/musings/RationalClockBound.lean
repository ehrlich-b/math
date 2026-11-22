import RationalClockPeriodic

/-!
# Finite bounds for integral periodic values

The argument uses signed finite binary weights. It does not require a real
infinite series or any identification between real and 2-adic limits.
-/

namespace RationalClockResearch

private def linearRuler (a b : ℤ) (n : ℕ) : ℤ :=
  a * n - 2 * b * rulerSum n

private theorem linearRuler_even (a b : ℤ) (n : ℕ) :
    linearRuler a b (2 * n) = 2 * linearRuler (a - b) b n := by
  simp only [linearRuler, rulerSum_two_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

private theorem linearRuler_odd (a b : ℤ) (n : ℕ) :
    linearRuler a b (2 * n + 1) =
      2 * linearRuler (a - b) b n + (a - 2 * b) := by
  simp only [linearRuler, rulerSum_two_mul_add_one, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_one]
  ring

private theorem binary_cases (n : ℕ) : (∃ m, n = 2 * m) ∨ (∃ m, n = 2 * m + 1) := by
  by_cases h : n % 2 = 0
  · exact Or.inl ⟨n / 2, by omega⟩
  · exact Or.inr ⟨n / 2, by omega⟩

private theorem allOnes_succ (L : ℕ) :
    2 ^ (L + 1) - 1 = 2 * (2 ^ L - 1) + 1 := by
  have h := pow_pos (by decide : 0 < (2 : ℕ)) L
  rw [pow_succ']
  omega

/-- Twice the ruler sum over all `L` one-bits. -/
theorem two_mul_rulerSum_allOnes (L : ℕ) :
    2 * rulerSum (2 ^ L - 1) = L * 2 ^ L := by
  induction L with
  | zero => simp [rulerSum]
  | succ L ih =>
      rw [allOnes_succ, rulerSum_two_mul_add_one, pow_succ']
      have h := pow_pos (by decide : 0 < (2 : ℕ)) L
      have hs : 2 ^ L - 1 + 1 = 2 ^ L := by omega
      nlinarith

private theorem linearRuler_allOnes (a b : ℤ) (L : ℕ) :
    linearRuler a b (2 ^ L - 1) =
      a * ((2 : ℤ) ^ L - 1) - b * L * (2 : ℤ) ^ L := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (two_mul_rulerSum_allOnes L)
  have hpow : 1 ≤ (2 : ℕ) ^ L := Nat.one_le_pow L 2 (by decide)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at h
  simp only [linearRuler, Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  linear_combination -b * h

private theorem linearRuler_nonneg_bounds (L n : ℕ) (a b : ℤ)
    (hn : n < 2 ^ L) (hb : 0 ≤ b) (ha : ((L : ℤ) + 1) * b ≤ a) :
    0 ≤ linearRuler a b n ∧
      linearRuler a b n ≤ linearRuler a b (2 ^ L - 1) := by
  induction L generalizing n a with
  | zero =>
      have hn0 : n = 0 := by simpa using hn
      subst n
      simp [linearRuler, rulerSum]
  | succ L ih =>
      have hshift : ((L : ℤ) + 1) * b ≤ a - b := by
        push_cast at ha
        linarith
      have hcoeff : 0 ≤ a - 2 * b := by
        have hLb : 0 ≤ (L : ℤ) * b := mul_nonneg (Int.natCast_nonneg L) hb
        push_cast at ha
        nlinarith
      rw [allOnes_succ, linearRuler_odd]
      rcases binary_cases n with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have hm : m < 2 ^ L := by rw [pow_succ'] at hn; omega
        have hi := ih m (a - b) hm hshift
        rw [linearRuler_even]
        constructor <;> linarith [hi.1, hi.2]
      · have hm : m < 2 ^ L := by rw [pow_succ'] at hn; omega
        have hi := ih m (a - b) hm hshift
        rw [linearRuler_odd]
        constructor <;> linarith [hi.1, hi.2]

private theorem linearRuler_complement (L n : ℕ) (a b : ℤ) (hn : n < 2 ^ L) :
    linearRuler a b n + linearRuler a b (2 ^ L - 1 - n) =
      linearRuler a b (2 ^ L - 1) := by
  induction L generalizing n a with
  | zero =>
      have hn0 : n = 0 := by simpa using hn
      subst n
      simp [linearRuler, rulerSum]
  | succ L ih =>
      have hpow : 0 < (2 : ℕ) ^ L := pow_pos (by decide) _
      rw [allOnes_succ]
      rcases binary_cases n with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have hm : m < 2 ^ L := by rw [pow_succ'] at hn; omega
        have hc : 2 * (2 ^ L - 1) + 1 - 2 * m =
            2 * (2 ^ L - 1 - m) + 1 := by omega
        rw [hc, linearRuler_even, linearRuler_odd, linearRuler_odd]
        linarith [ih m (a - b) hm]
      · have hm : m < 2 ^ L := by rw [pow_succ'] at hn; omega
        have hc : 2 * (2 ^ L - 1) + 1 - (2 * m + 1) =
            2 * (2 ^ L - 1 - m) := by omega
        rw [hc, linearRuler_odd, linearRuler_even, linearRuler_odd]
        linarith [ih m (a - b) hm]

/-- A uniform finite bound for the signed periodic ruler discrepancy. -/
theorem periodic_discrepancy_bound (L B : ℕ) (hB : B < 2 ^ L) :
    -((2 : ℤ) ^ L - 1) ^ 2 ≤
        2 * ((L : ℤ) * (2 : ℤ) ^ L * B -
          2 * ((2 : ℤ) ^ L - 1) * rulerSum B) ∧
      2 * ((L : ℤ) * (2 : ℤ) ^ L * B -
        2 * ((2 : ℤ) ^ L - 1) * rulerSum B) ≤ ((2 : ℤ) ^ L - 1) ^ 2 := by
  cases L with
  | zero => simp
  | succ k =>
      let Q : ℤ := (2 : ℤ) ^ (k + 1)
      let M : ℤ := Q - 1
      let a : ℤ := ((k : ℤ) + 1) * Q
      have hk : 0 ≤ (k : ℤ) := Int.natCast_nonneg k
      have hQ : 1 ≤ Q := by
        dsimp [Q]
        exact_mod_cast Nat.one_le_pow (k + 1) 2 (by decide)
      have hM : 0 ≤ M := by dsimp [M]; omega
      have ha : ((k : ℤ) + 1) * M ≤ a := by dsimp [M, a]; nlinarith
      have hmax : 2 * linearRuler a M (2 ^ k - 1) ≤ M ^ 2 := by
        rw [linearRuler_allOnes]
        dsimp [a, M, Q]
        rw [pow_succ']
        nlinarith [mul_nonneg hk (show 0 ≤ (2 : ℤ) ^ k by positivity)]
      have hlower : ∀ b : ℕ, b < 2 ^ k →
          0 ≤ linearRuler a M b ∧ 2 * linearRuler a M b ≤ M ^ 2 := by
        intro b hb
        have hi := linearRuler_nonneg_bounds k b a M hb hM ha
        exact ⟨hi.1, by linarith [hi.2]⟩
      simp only [Nat.cast_add, Nat.cast_one]
      change -M ^ 2 ≤ 2 * linearRuler a M B ∧ 2 * linearRuler a M B ≤ M ^ 2
      by_cases hhalf : B < 2 ^ k
      · have hi := hlower B hhalf
        exact ⟨by nlinarith [sq_nonneg M, hi.1], hi.2⟩
      · have hc : 2 ^ (k + 1) - 1 - B < 2 ^ k := by
          rw [pow_succ'] at hB ⊢
          omega
        have hi := hlower (2 ^ (k + 1) - 1 - B) hc
        have heq := linearRuler_complement (k + 1) B a M hB
        have hall : linearRuler a M (2 ^ (k + 1) - 1) = 0 := by
          rw [linearRuler_allOnes]
          dsimp [a, M, Q]
          ring
        rw [hall] at heq
        constructor <;> nlinarith [hi.1, hi.2, sq_nonneg M]

/-- The periodic value lies strictly between `-c` and `c+1`, expressed after
clearing its positive denominator. These bounds suffice for the integral phase
classification, even though the real-series argument gives sharper endpoints. -/
theorem periodicNumerator_strict_bounds (c L B : ℕ)
    (hB0 : 0 < B) (hBM : B < 2 ^ L - 1) :
    -(c : ℤ) * ((2 : ℤ) ^ L - 1) ^ 2 < periodicNumerator c L B ∧
      periodicNumerator c L B < ((c : ℤ) + 1) * ((2 : ℤ) ^ L - 1) ^ 2 := by
  let M : ℤ := (2 : ℤ) ^ L - 1
  let H : ℤ := (L : ℤ) * (2 : ℤ) ^ L * B - 2 * M * rulerSum B
  have hpow : 1 ≤ (2 : ℕ) ^ L := Nat.one_le_pow L 2 (by decide)
  have hcast : ((2 ^ L - 1 : ℕ) : ℤ) = M := by
    simp only [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, M]
  have hBMZ : (B : ℤ) < M := by
    rw [← hcast]
    exact_mod_cast hBM
  have hB0Z : 0 < (B : ℤ) := by exact_mod_cast hB0
  have hM : 0 < M := lt_trans hB0Z hBMZ
  have hBpow : B < 2 ^ L := by omega
  have hd := periodic_discrepancy_bound L B hBpow
  change -M ^ 2 ≤ 2 * H ∧ 2 * H ≤ M ^ 2 at hd
  have hN : periodicNumerator c L B =
      M ^ 2 - (B : ℤ) * M + 2 * c * H := by
    simp only [periodicNumerator, closed, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat, M, H]
    ring
  have hlo : 0 ≤ (c : ℤ) * (2 * H + M ^ 2) :=
    mul_nonneg (Int.natCast_nonneg c) (by linarith [hd.1])
  have hhi : 0 ≤ (c : ℤ) * (M ^ 2 - 2 * H) :=
    mul_nonneg (Int.natCast_nonneg c) (by linarith [hd.2])
  change -(c : ℤ) * M ^ 2 < periodicNumerator c L B ∧
    periodicNumerator c L B < ((c : ℤ) + 1) * M ^ 2
  constructor
  · nlinarith [mul_pos hM (sub_pos.mpr hBMZ)]
  · nlinarith [mul_pos hB0Z hM]

/-- Every integral, nonconstant periodic-block value lies in the finite
candidate interval `{1-c, ..., c}`. -/
theorem periodic_integral_bounds (c L B : ℕ) (seed : ℤ)
    (hB0 : 0 < B) (hBM : B < 2 ^ L - 1)
    (hvalue : periodicNumerator c L B = ((2 : ℤ) ^ L - 1) ^ 2 * seed) :
    (1 : ℤ) - c ≤ seed ∧ seed ≤ c := by
  have h := periodicNumerator_strict_bounds c L B hB0 hBM
  have hpow : 1 ≤ (2 : ℕ) ^ L := Nat.one_le_pow L 2 (by decide)
  have hM : 0 < (2 : ℤ) ^ L - 1 := by
    have hnat : 1 < (2 : ℕ) ^ L := by omega
    exact sub_pos.mpr (by exact_mod_cast hnat)
  have hM2 : 0 < ((2 : ℤ) ^ L - 1) ^ 2 := sq_pos_of_pos hM
  rw [hvalue] at h
  have hlo : -(c : ℤ) < seed :=
    (mul_lt_mul_iff_left₀ hM2).mp (by simpa only [mul_comm] using h.1)
  have hhi : seed < (c : ℤ) + 1 :=
    (mul_lt_mul_iff_left₀ hM2).mp (by simpa only [mul_comm] using h.2)
  omega

end RationalClockResearch

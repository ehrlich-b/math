import RationalClockRepresentation
import RationalClockPeriodic
import RationalClockBound

/-!
# Every rational interior phase has a finite repeated block

Euler's theorem provides a period for every odd denominator.  No minimal
period, denominator cutoff, or search certificate is required.
-/

namespace RationalClockResearch

/-- The finite repeated-block representation of every phase in `(-1, 0)`. -/
theorem exists_periodic_block {theta : ℚ} (hodd : Odd theta.den)
    (hlo : -1 < theta) (hhi : theta < 0) :
    ∃ L B : ℕ, 0 < L ∧ 0 < B ∧ B < 2 ^ L - 1 ∧
      ((2 : ℤ) ^ L - 1) * theta.num = -(theta.den : ℤ) * B := by
  have hdq : (0 : ℚ) < theta.den := by exact_mod_cast theta.den_pos
  have heq : (theta.num : ℚ) = theta * theta.den :=
    (div_eq_iff (ne_of_gt hdq)).mp theta.num_div_den
  have hnq : (theta.num : ℚ) < 0 := by rw [heq]; exact mul_neg_of_neg_of_pos hhi hdq
  have hn : theta.num < 0 := by exact_mod_cast hnq
  have hndq : -(theta.den : ℚ) < theta.num := by
    have hh := mul_lt_mul_of_pos_right hlo hdq
    rw [← heq] at hh
    simpa using hh
  have hnd : -(theta.den : ℤ) < theta.num := by exact_mod_cast hndq
  let a := (-theta.num).toNat
  have haZ : (a : ℤ) = -theta.num := Int.toNat_of_nonneg (by omega)
  have ha : 0 < a := by omega
  have had : a < theta.den := by omega
  let L := Nat.totient theta.den
  have hL : 0 < L := Nat.totient_pos.mpr theta.den_pos
  have hp : 1 < 2 ^ L := Nat.one_lt_pow (by omega) (by omega)
  have hmod : Nat.ModEq theta.den (2 ^ L) 1 :=
    Nat.ModEq.pow_totient hodd.coprime_two_right.symm
  have hdvd : theta.den ∣ 2 ^ L - 1 := hmod.symm.dvd'
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    by_contra hh
    have hk0 : k = 0 := by omega
    rw [hk0, mul_zero] at hk
    omega
  refine ⟨L, k * a, hL, Nat.mul_pos hkpos ha, ?_, ?_⟩
  · rw [hk]
    nlinarith
  · have hkZ : (2 : ℤ) ^ L - 1 = (theta.den : ℤ) * k := by
      have hh := congrArg (fun n : ℕ => (n : ℤ)) hk
      rw [Int.natCast_sub (by omega : 1 ≤ 2 ^ L)] at hh
      simpa using hh
    rw [hkZ, Nat.cast_mul, haZ]
    ring

/-- The full integral phase bound, uniformly over every odd denominator. -/
theorem integralPhaseBound : IntegralPhaseBoundClaim := by
  intro c theta seed _hc hlo hhi h
  obtain ⟨L, B, hL, hB0, hBM, hclock⟩ := exists_periodic_block h.1 hlo hhi
  have hvalue := periodicNumerator_eq_of_represents hL (by omega : B < 2 ^ L) hclock h
  have hbounds := periodic_integral_bounds c L B seed hB0 hBM hvalue
  have hne := represents_phase_ne_zero_one hlo hhi h
  exact ⟨hbounds.1, hbounds.2, hne.1, hne.2⟩

/-- The only four integral noninteger coefficient-twelve phases. -/
theorem coefficientTwelvePhase : CoefficientTwelvePhaseClaim := by
  intro theta seed hlo hhi
  constructor
  · intro h
    have hb := integralPhaseBound 3 theta seed (by decide) hlo hhi h
    have hs : seed = 2 ∨ seed = -1 ∨ seed = 3 ∨ seed = -2 := by omega
    rcases hs with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨represents_clock_unique h represents_three_neg_one_third, rfl⟩
    · exact Or.inr (Or.inl ⟨represents_clock_unique h represents_three_neg_two_thirds, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨represents_clock_unique h represents_three_neg_two_ninths, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨represents_clock_unique h represents_three_neg_seven_ninths, rfl⟩))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact represents_three_neg_one_third
    · exact represents_three_neg_two_thirds
    · exact represents_three_neg_two_ninths
    · exact represents_three_neg_seven_ninths

theorem no_original_integral_phase {theta : ℚ} {seed : ℤ}
    (hlo : -1 < theta) (hhi : theta < 0) : ¬ represents 1 theta seed := by
  intro h
  have hb := integralPhaseBound 1 theta seed (by decide) hlo hhi h
  omega

end RationalClockResearch

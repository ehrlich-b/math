import RationalClockPadic

/-!
# Rational points inside the 2-adic clock

Rationals with odd denominator embed canonically in `ℤ_[2]`.  The finite
`represents` predicate is exactly equality between the lifted 2-adic clock of
that rational point and the integer seed.  This identifies the original
classification interface with the genuine 2-adic construction.
-/

namespace RationalClockResearch

/-- A rational with odd denominator, regarded as a 2-adic integer. -/
noncomputable def rationalPadicInt (theta : ℚ) (hodd : Odd theta.den) : ℤ_[2] :=
  ⟨(theta : ℚ_[2]), Padic.norm_rat_le_one hodd.not_two_dvd_nat⟩

theorem rationalPadicInt_mul_den (theta : ℚ) (hodd : Odd theta.den) :
    rationalPadicInt theta hodd * (theta.den : ℤ_[2]) =
      (theta.num : ℤ_[2]) := by
  apply PadicInt.ext
  change (theta : ℚ_[2]) * theta.den = theta.num
  norm_cast
  exact Rat.mul_den_eq_num theta

/-- The residue of a rational 2-adic integer is characterized by the same
linear congruence used in `represents`. -/
theorem rationalPadicInt_toZModPow_eq_iff (theta : ℚ)
    (hodd : Odd theta.den) (K m : ℕ) :
    PadicInt.toZModPow K (rationalPadicInt theta hodd) =
        (m : ZMod (2 ^ K)) ↔
      Int.ModEq (2 ^ K) ((theta.den : ℤ) * (m : ℤ)) theta.num := by
  have hrel := congrArg (PadicInt.toZModPow K)
    (rationalPadicInt_mul_den theta hodd)
  simp only [map_mul, map_natCast, map_intCast] at hrel
  have hrel' : (theta.den : ZMod (2 ^ K)) *
      PadicInt.toZModPow K (rationalPadicInt theta hodd) =
        (theta.num : ZMod (2 ^ K)) := by
    simpa only [mul_comm] using hrel
  have hcop : theta.den.Coprime (2 ^ K) :=
    hodd.coprime_two_right.pow_right K
  have hunit : IsUnit (theta.den : ZMod (2 ^ K)) := by
    simpa only [ZMod.coe_unitOfCoprime] using
      (ZMod.unitOfCoprime theta.den hcop).isUnit
  constructor
  · intro hm
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [← hm]
    exact hrel'
  · intro hm
    have hmZ : (theta.den : ZMod (2 ^ K)) * (m : ZMod (2 ^ K)) =
        (theta.num : ZMod (2 ^ K)) := by
      have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hm
      simpa only [Int.cast_mul, Int.cast_natCast] using this
    exact hunit.mul_left_cancel (hrel'.trans hmZ.symm)

/-- The original finite-residue predicate is precisely equality in `ℤ_[2]`. -/
theorem represents_iff_padicClock_eq {c : ℕ} {theta : ℚ} {seed : ℤ}
    (hodd : Odd theta.den) :
    represents c theta seed ↔
      padicClock c (rationalPadicInt theta hodd) = (seed : ℤ_[2]) := by
  constructor
  · intro h
    apply PadicInt.ext_of_toZModPow.mp
    intro K
    let m := (PadicInt.toZModPow K (rationalPadicInt theta hodd)).val
    have hmres : PadicInt.toZModPow K (rationalPadicInt theta hodd) =
        (m : ZMod (2 ^ K)) := (ZMod.natCast_zmod_val _).symm
    have hm := (rationalPadicInt_toZModPow_eq_iff theta hodd K m).mp hmres
    have hclosed := h.2 K m hm
    rw [padicClock_toZModPow]
    change (closed c m : ZMod (2 ^ K)) =
      PadicInt.toZModPow K (seed : ℤ_[2])
    simp only [map_intCast]
    rw [← Int.cast_natCast]
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr hclosed
  · intro hclock
    refine ⟨hodd, ?_⟩
    intro K m hm
    have hmres :=
      (rationalPadicInt_toZModPow_eq_iff theta hodd K m).mpr hm
    have hclockRes := congrArg (PadicInt.toZModPow K) hclock
    rw [padicClock_toZModPow, hmres, closedResidue_natCast] at hclockRes
    simp only [map_intCast] at hclockRes
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simpa only [Int.cast_natCast] using hclockRes

/-- Proof-irrelevant existential form of the rational-point bridge. -/
theorem represents_iff_exists_padicClock_eq {c : ℕ} {theta : ℚ} {seed : ℤ} :
    represents c theta seed ↔
      ∃ hodd : Odd theta.den,
        padicClock c (rationalPadicInt theta hodd) = (seed : ℤ_[2]) := by
  constructor
  · intro h
    exact ⟨h.1, (represents_iff_padicClock_eq h.1).mp h⟩
  · rintro ⟨hodd, hclock⟩
    exact (represents_iff_padicClock_eq hodd).mpr hclock

/-- Consolidated 2-adic endpoint: bijectivity, isometry, explicit conjugacy,
minimal dynamics, and exact agreement with the finite rational-clock
interface. -/
theorem padicClockTheory :
    (∀ c : ℕ, Function.Bijective (padicClock c)) ∧
    (∀ c : ℕ, Isometry (padicClock c)) ∧
    (∀ (c : ℕ) (z : ℤ_[2]),
      padicClock c (z + 1) =
        padicClock c z + ((4 * c : ℕ) : ℤ_[2]) *
          padicLow (padicClock c z) + 1) ∧
    (∀ (c : ℕ) (x : ℤ_[2]),
      DenseRange (fun n : ℕ => (padicStep c)^[n] x)) ∧
    (∀ (c : ℕ) (theta : ℚ) (seed : ℤ),
      represents c theta seed ↔
        ∃ hodd : Odd theta.den,
          padicClock c (rationalPadicInt theta hodd) = (seed : ℤ_[2])) := by
  refine ⟨?_, padicClock_isometry, padicClock_explicit_conjugacy,
    padicStep_orbit_dense, ?_⟩
  · intro c
    exact (padicClockEquiv c).bijective
  · intro c theta seed
    exact represents_iff_exists_padicClock_eq

end RationalClockResearch

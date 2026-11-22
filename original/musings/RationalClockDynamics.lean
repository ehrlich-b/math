import RationalClockRepresentation
import RationalClockValuation

/-!
# Transporting rational clocks along positive orbits

All clock transport is through finite congruences.  The valuation of a positive
represented seed is recovered at a precision just beyond its first nonzero bit.
-/

namespace RationalClockResearch

theorem rat_add_nat_num (theta : ℚ) (t : ℕ) :
    (theta + t).num = theta.num + (t : ℤ) * theta.den := by
  have h := Rat.add_num_den' theta (t : ℚ)
  simp only [Rat.den_natCast, Rat.num_natCast, Nat.cast_one, mul_one,
    Rat.add_natCast_den] at h
  exact mul_right_cancel₀ (Int.ofNat_ne_zero.mpr theta.den_nz) h

/-- The shifted rational numerator gives the valuation of a positive seed,
provided that numerator is positive. -/
theorem represents_valuation {c seed : ℕ} {theta : ℚ}
    (h : represents c theta (seed : ℤ)) (hseed : 0 < seed)
    (hnum : 0 < theta.num + (theta.den : ℤ)) :
    padicValNat 2 seed = padicValNat 2 (theta.num + (theta.den : ℤ)).toNat := by
  let K := padicValNat 2 seed + 1
  obtain ⟨m, hm⟩ := exists_index_mod theta h.1 K
  have hc : Nat.ModEq (2 ^ K) (closed c m) seed := by
    exact Int.natCast_modEq_iff.mp (by exact_mod_cast h.2 K m hm)
  have hv : padicValNat 2 seed = padicValNat 2 (m + 1) := by
    have hh := valuation_eq_of_modEq hseed (closed_pos c m) hc.symm
      (show padicValNat 2 seed < K by omega)
    simpa only [closed_valuation] using hh
  have hd : padicValNat 2 theta.den = 0 :=
    padicValNat.eq_zero_of_not_dvd h.1.not_two_dvd_nat
  have hprod : padicValNat 2 (theta.den * (m + 1)) = padicValNat 2 seed := by
    rw [padicValNat.mul theta.den_nz (Nat.succ_ne_zero m), hd, zero_add, hv]
  have hi : Int.ModEq (2 ^ K) ((theta.den * (m + 1) : ℕ) : ℤ)
      (theta.num + (theta.den : ℤ)) := by
    convert hm.add_right (theta.den : ℤ) using 1
    push_cast
    ring
  have hin : Nat.ModEq (2 ^ K) (theta.den * (m + 1))
      (theta.num + (theta.den : ℤ)).toNat := by
    apply Int.natCast_modEq_iff.mp
    simpa only [Int.toNat_of_nonneg (le_of_lt hnum), Nat.cast_pow, Nat.cast_ofNat] using hi
  have hh := valuation_eq_of_modEq (Nat.mul_pos theta.den_pos (by omega))
    (by omega) hin (by rw [hprod]; omega)
  exact hprod.symm.trans hh

/-- Shift a nonzero signed represented seed by one clock tick.  The low part
uses the absolute value; zero is deliberately excluded. -/
theorem represents_add_one {c : ℕ} {theta : ℚ} {seed : ℤ}
    (h : represents c theta seed) (hseed : seed ≠ 0) :
    represents c (theta + 1) (seed + 4 * c * (low seed.natAbs : ℤ) + 1) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro K m hm
  have hnum : (theta + 1).num = theta.num + (theta.den : ℤ) := by
    simpa using rat_add_nat_num theta 1
  simp only [Rat.add_ofNat_den, hnum] at hm
  let n := m + (2 ^ K - 1)
  have hp : 1 ≤ 2 ^ K := Nat.one_le_pow K 2 (by omega)
  have hn : (n : ℤ) = (m : ℤ) + 2 ^ K - 1 := by
    dsimp [n]
    rw [Int.natCast_sub hp]
    push_cast
    ring
  have hi : Int.ModEq (2 ^ K) ((theta.den : ℤ) * (n : ℤ)) theta.num := by
    obtain ⟨q, hq⟩ := hm.dvd
    apply Int.modEq_iff_dvd.mpr
    refine ⟨q - (theta.den : ℤ), ?_⟩
    rw [hn]
    linear_combination hq
  have hc := h.2 K n hi
  have hl := signed_low_modEq_of_modEq
    (show (closed c n : ℤ) ≠ 0 by exact_mod_cast (ne_of_gt (closed_pos c n))) hseed hc
  simp only [Int.natAbs_natCast] at hl
  have hsucc : Int.ModEq (2 ^ K) (closed c (n + 1) : ℤ)
      (seed + 4 * c * (low seed.natAbs : ℤ) + 1) := by
    have hh := (hc.add (hl.mul_left (4 * c))).add_right 1
    rw [closed_succ_eq_step_of_low_eq c n (closed_low c n)]
    simpa [step] using hh
  have hmn : Int.ModEq (2 ^ K) (m : ℤ) ((n + 1 : ℕ) : ℤ) := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨1, ?_⟩
    push_cast
    rw [hn]
    ring
  exact ((closed_modEq_iff c K m (n + 1)).mpr hmn).trans hsucc

theorem represents_step {c seed : ℕ} {theta : ℚ}
    (h : represents c theta (seed : ℤ)) (hseed : 0 < seed) :
    represents c (theta + 1) (step c seed : ℤ) := by
  simpa [step] using represents_add_one h (by exact_mod_cast (ne_of_gt hseed))

/-- A rational clock advances by an ordinary integer along its positive orbit. -/
theorem represents_orbit {c seed : ℕ} {theta : ℚ}
    (h : represents c theta (seed : ℤ)) (hseed : 0 < seed) (t : ℕ) :
    represents c (theta + t) (orbit c seed t : ℤ) := by
  induction t with
  | zero => simpa [orbit] using h
  | succ t ih =>
      simpa [orbit, Nat.cast_add, add_assoc] using
        represents_step ih (orbit_pos hseed)

theorem hasRationalClock_orbit {c seed : ℕ} (h : hasRationalClock c seed)
    (hseed : 0 < seed) (t : ℕ) : hasRationalClock c (orbit c seed t) := by
  obtain ⟨theta, htheta⟩ := h
  exact ⟨theta + t, represents_orbit htheta hseed t⟩

end RationalClockResearch

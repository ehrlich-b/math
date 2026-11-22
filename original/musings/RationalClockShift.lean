import RationalClockDynamics

/-!
# Signed integer shifts of nonintegral rational clocks

Backward shifts use the rational clock numerator to recover the predecessor's
low part. All uses of the signed low part explicitly exclude zero.
-/

namespace RationalClockResearch

theorem rat_sub_one_num (theta : ℚ) :
    (theta - 1).num = theta.num - (theta.den : ℤ) := by
  have h := rat_add_nat_num (theta - 1) 1
  simp only [Nat.cast_one, sub_add_cancel, Rat.sub_ofNat_den, one_mul] at h
  omega

/-- Recover the represented seed one clock tick earlier, provided the current
clock is nonzero. The exceptional transition from clock `-1` to `0` is excluded. -/
theorem represents_sub_one {c : ℕ} {theta : ℚ} {seed : ℤ}
    (h : represents c theta seed) (htheta : theta ≠ 0) :
    represents c (theta - 1) (seed - 1 - 4 * c * (low theta.num.natAbs : ℤ)) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro K m hm
  simp only [Rat.sub_ofNat_den, rat_sub_one_num] at hm
  have hi : Int.ModEq (2 ^ K) ((theta.den * (m + 1) : ℕ) : ℤ) theta.num := by
    convert hm.add_right (theta.den : ℤ) using 1 <;> push_cast <;> ring
  have hc := h.2 K (m + 1) (by simpa only [Nat.cast_mul] using hi)
  have hp : theta.den * (m + 1) ≠ 0 := Nat.mul_ne_zero theta.den_nz (Nat.succ_ne_zero m)
  have hl := signed_low_modEq_of_modEq (by exact_mod_cast hp)
    (Rat.num_ne_zero.mpr htheta) hi
  have hv : low (theta.den * (m + 1)) = low (m + 1) := by
    rw [low, low, padicValNat.mul theta.den_nz (Nat.succ_ne_zero m),
      padicValNat.eq_zero_of_not_dvd h.1.not_two_dvd_nat, zero_add]
  simp only [Int.natAbs_natCast, hv] at hl
  have hs : (closed c (m + 1) : ℤ) =
      (closed c m : ℤ) + 1 + 4 * c * (low (m + 1) : ℤ) := by
    exact_mod_cast closed_succ c m
  convert hc.sub ((hl.mul_left (4 * c)).add_left 1) using 1 <;> linarith

private theorem nonintegral_add_int {theta : ℚ}
    (h : ∀ z : ℤ, theta ≠ (z : ℚ)) (j : ℤ) :
    ∀ z : ℤ, theta + j ≠ (z : ℚ) := by
  intro z hz
  apply h (z - j)
  push_cast
  linarith

/-- Every integer translate of a represented nonintegral clock still represents
an ordinary integer seed, possibly negative. -/
theorem represents_int_shift {c : ℕ} {theta : ℚ} {seed : ℤ}
    (h : represents c theta seed) (hnon : ∀ z : ℤ, theta ≠ (z : ℚ)) (j : ℤ) :
    ∃ s : ℤ, represents c (theta + j) s := by
  induction j using Int.induction_on with
  | zero => exact ⟨seed, by simpa using h⟩
  | succ j ih =>
      obtain ⟨s, hs⟩ := ih
      have hne : s ≠ 0 := by
        intro hz
        subst s
        have he := (represents_seed_zero_iff c (theta + j)).mp hs
        exact nonintegral_add_int hnon j (-1) (by simpa using he)
      refine ⟨s + 4 * c * (low s.natAbs : ℤ) + 1, ?_⟩
      simpa only [Int.cast_add, Int.cast_one, add_assoc] using represents_add_one hs hne
  | pred j ih =>
      obtain ⟨s, hs⟩ := ih
      have hne : theta + ((-(j : ℤ)) : ℚ) ≠ 0 := by
        simpa using nonintegral_add_int hnon (-(j : ℤ)) 0
      have hs' := represents_sub_one hs hne
      refine ⟨s - 1 - 4 * c * (low (theta + ((-(j : ℤ)) : ℚ)).num.natAbs : ℤ), ?_⟩
      convert hs' using 1 <;> push_cast <;> ring

end RationalClockResearch

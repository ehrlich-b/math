import RationalClockIsometry

/-!
# Uniqueness and endpoint values of rational clocks

The finite-residue definition supplies an actual lift at every precision.
Combining this with finite isometry makes the represented rational clock
unique as well as the represented seed.
-/

namespace RationalClockResearch

/-- The all-ones binary index has a closed form divisible by its precision. -/
theorem closed_two_pow_sub_one (c K : ℕ) :
    closed c (2 ^ K - 1) = 2 ^ K * (1 + 2 * c * K) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hp : 1 ≤ 2 ^ K := Nat.one_le_pow K 2 (by omega)
      have he : 2 ^ (K + 1) - 1 = 2 * (2 ^ K - 1) + 1 := by
        rw [pow_succ]
        omega
      rw [he, closed_two_mul_add_one, ih, pow_succ]
      have hs := Nat.sub_add_cancel hp
      nlinarith

/-- Clock uniqueness reduced to the precise finite isometry obligation. -/
theorem represents_clock_unique_of_isometry {c : ℕ}
    (hiso : ∀ K m n : ℕ,
      Int.ModEq (2 ^ K) (closed c m : ℤ) (closed c n : ℤ) ↔
        Int.ModEq (2 ^ K) (m : ℤ) (n : ℤ))
    {theta eta : ℚ} {seed : ℤ}
    (htheta : represents c theta seed) (heta : represents c eta seed) :
    theta = eta := by
  let delta : ℤ := eta.num * theta.den - theta.num * eta.den
  let K := delta.natAbs
  obtain ⟨m, hm⟩ := exists_index_mod theta htheta.1 K
  obtain ⟨n, hn⟩ := exists_index_mod eta heta.1 K
  have hmn : Int.ModEq (2 ^ K) (m : ℤ) (n : ℤ) :=
    (hiso K m n).mp ((htheta.2 K m hm).trans (heta.2 K n hn).symm)
  have hcross : Int.ModEq (2 ^ K)
      (theta.num * eta.den) (eta.num * theta.den) := by
    calc
      theta.num * eta.den ≡ ((theta.den : ℤ) * m) * eta.den [ZMOD 2 ^ K] :=
        (hm.mul_right _).symm
      _ ≡ ((theta.den : ℤ) * n) * eta.den [ZMOD 2 ^ K] :=
        (hmn.mul_left _).mul_right _
      _ ≡ ((eta.den : ℤ) * n) * theta.den [ZMOD 2 ^ K] := by
        convert Int.ModEq.refl (((theta.den : ℤ) * n) * eta.den) using 1
        ring
      _ ≡ eta.num * theta.den [ZMOD 2 ^ K] := hn.mul_right _
  have hdvd : ((2 ^ K : ℕ) : ℤ) ∣ delta := hcross.dvd
  have hlt : delta.natAbs < Int.natAbs ((2 ^ K : ℕ) : ℤ) := by
    simp only [Int.natAbs_natCast]
    exact Nat.lt_two_pow_self
  have hzero : delta = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt
  have heq : theta.num * (eta.den : ℤ) = eta.num * (theta.den : ℤ) := by
    dsimp [delta] at hzero
    omega
  rw [← Rat.num_divInt_den theta, ← Rat.num_divInt_den eta]
  exact (Rat.divInt_eq_divInt_iff
    (Int.ofNat_ne_zero.mpr theta.den_nz) (Int.ofNat_ne_zero.mpr eta.den_nz)).mpr heq

/-- A represented seed has at most one rational clock. -/
theorem represents_clock_unique {c : ℕ} {theta eta : ℚ} {seed : ℤ}
    (htheta : represents c theta seed) (heta : represents c eta seed) :
    theta = eta :=
  represents_clock_unique_of_isometry (closed_modEq_iff c) htheta heta

/-- Each nonnegative integer is the clock of its closed-form seed. -/
theorem represents_nat (c n : ℕ) : represents c (n : ℚ) (closed c n : ℤ) := by
  refine ⟨by simp, ?_⟩
  intro K m hm
  apply (closed_modEq_iff c K m n).mpr
  simpa using hm

theorem hasRationalClock_closed (c n : ℕ) : hasRationalClock c (closed c n) :=
  ⟨n, represents_nat c n⟩

@[simp] theorem represents_zero (c : ℕ) : represents c 0 1 := by
  simpa using represents_nat c 0

/-- The all-ones residues give the exceptional clock value `F(-1) = 0`. -/
theorem represents_neg_one (c : ℕ) : represents c (-1) 0 := by
  refine ⟨by norm_num, ?_⟩
  intro K m hm
  have hp : 1 ≤ 2 ^ K := Nat.one_le_pow K 2 (by omega)
  have hq : Int.ModEq (2 ^ K) ((2 ^ K - 1 : ℕ) : ℤ) (-1) := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-1, ?_⟩
    rw [Int.natCast_sub hp]
    push_cast
    ring
  have hi : Int.ModEq (2 ^ K) (m : ℤ) ((2 ^ K - 1 : ℕ) : ℤ) := by
    exact (by simpa using hm : Int.ModEq (2 ^ K) (m : ℤ) (-1)).trans hq.symm
  have hc := (closed_modEq_iff c K m (2 ^ K - 1)).mpr hi
  apply hc.trans
  rw [closed_two_pow_sub_one, Int.natCast_mul, Int.natCast_pow, Nat.cast_ofNat]
  exact (dvd_mul_right _ _).modEq_zero_int

theorem represents_seed_zero_iff (c : ℕ) (theta : ℚ) :
    represents c theta 0 ↔ theta = -1 := by
  constructor
  · intro h
    exact represents_clock_unique h (represents_neg_one c)
  · rintro rfl
    exact represents_neg_one c

theorem represents_seed_one_iff (c : ℕ) (theta : ℚ) :
    represents c theta 1 ↔ theta = 0 := by
  constructor
  · intro h
    exact represents_clock_unique h (represents_zero c)
  · rintro rfl
    exact represents_zero c

/-- The two endpoint values cannot be attained by an interior rational phase. -/
theorem represents_phase_ne_zero_one {c : ℕ} {theta : ℚ} {seed : ℤ}
    (hlo : -1 < theta) (hhi : theta < 0) (h : represents c theta seed) :
    seed ≠ 0 ∧ seed ≠ 1 := by
  constructor
  · intro hs
    rw [hs, represents_seed_zero_iff] at h
    linarith
  · intro hs
    rw [hs, represents_seed_one_iff] at h
    linarith

end RationalClockResearch

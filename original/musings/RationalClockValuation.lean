import RationalClockBasic

/-!
# Valuations and the orbit from one

The binary recurrences for `rulerSum` suffice to compute the valuation of
`closed`, independently of the finite-clock isometry.  In particular, all
natural coefficients have the same valuation clock on the orbit from one.
-/

namespace RationalClockResearch

theorem low_dvd (n : ℕ) : low n ∣ n :=
  pow_padicValNat_dvd

theorem low_le {n : ℕ} (hn : 0 < n) : low n ≤ n :=
  Nat.le_of_dvd hn (low_dvd n)

theorem closed_pos (c n : ℕ) : 0 < closed c n := by
  simp only [closed]
  omega

/-- The ruler sum has enough factors of two to leave the leading valuation
of `n + 1` unchanged in the closed orbit formula. -/
theorem low_succ_dvd_two_mul_rulerSum (n : ℕ) :
    low (n + 1) ∣ 2 * rulerSum n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases heven : n % 2 = 0
      · have hn : n = 2 * (n / 2) := by omega
        rw [hn, low_two_mul_add_one]
        exact one_dvd _
      · have hn : n = 2 * (n / 2) + 1 := by omega
        have hsmaller : n / 2 < n := by omega
        have hsum := dvd_add (low_dvd (n / 2 + 1)) (ih (n / 2) hsmaller)
        rw [hn, show (2 * (n / 2) + 1) + 1 = 2 * (n / 2 + 1) by omega]
        rw [low_two_mul_succ, rulerSum_two_mul_add_one]
        convert Nat.mul_dvd_mul_left 2 hsum using 1
        ring

theorem closed_valuation (c n : ℕ) :
    padicValNat 2 (closed c n) = padicValNat 2 (n + 1) := by
  have hcorrection : 2 ^ (padicValNat 2 (n + 1) + 1) ∣ 4 * c * rulerSum n := by
    obtain ⟨q, hq⟩ := low_succ_dvd_two_mul_rulerSum n
    refine ⟨c * q, ?_⟩
    simp only [low] at hq
    rw [pow_succ]
    nlinarith [congrArg (fun x : ℕ => 2 * c * x) hq]
  have hdiv : 2 ^ padicValNat 2 (n + 1) ∣ closed c n := by
    exact dvd_add pow_padicValNat_dvd
      ((pow_dvd_pow 2 (Nat.le_succ _)).trans hcorrection)
  have hlower := (padicValNat_dvd_iff_le (ne_of_gt (closed_pos c n))).mp hdiv
  have hnot : ¬2 ^ (padicValNat 2 (n + 1) + 1) ∣ closed c n := by
    intro h
    have hbase : 2 ^ (padicValNat 2 (n + 1) + 1) ∣ n + 1 := by
      exact (Nat.dvd_add_iff_left hcorrection).mpr h
    exact pow_succ_padicValNat_not_dvd (Nat.succ_ne_zero n) hbase
  have hupper := mt (padicValNat_dvd_iff_le (ne_of_gt (closed_pos c n))).mpr hnot
  omega

theorem closed_low (c n : ℕ) : low (closed c n) = low (n + 1) := by
  simp only [low, closed_valuation]

theorem orbit_one_eq_closed (c t : ℕ) : orbit c 1 t = closed c t :=
  orbit_one_eq_closed_of_low_eq c (closed_low c) t

theorem orbit_one_valuation (c t : ℕ) :
    padicValNat 2 (orbit c 1 t) = padicValNat 2 (t + 1) := by
  rw [orbit_one_eq_closed, closed_valuation]

/-- Every step adds at least `4*c + 1`, since the low part is positive. -/
theorem orbit_linear_growth (c seed t : ℕ) :
    seed + (4 * c + 1) * t ≤ orbit c seed t := by
  induction t with
  | zero => simp [orbit]
  | succ t ih =>
      rw [orbit, step]
      have hlow := low_pos (orbit c seed t)
      nlinarith

@[simp] theorem low_two_pow (k : ℕ) : low (2 ^ k) = 2 ^ k := by
  simp [low]

/-- A valuation clock bounds any exact power-of-two hit by its clock value. -/
theorem power_hit_le_clock {x clock k : ℕ} (hclock : 0 < clock)
    (hval : padicValNat 2 x = padicValNat 2 clock) (hhit : x = 2 ^ k) :
    x ≤ clock := by
  have hlow : low x = low clock := by simp only [low, hval]
  rw [hhit, low_two_pow] at hlow
  rw [hhit, hlow]
  exact low_le hclock

theorem orbit_power_hit_le_clock {c seed t clock k : ℕ} (hclock : 0 < clock)
    (hval : padicValNat 2 (orbit c seed t) = padicValNat 2 clock)
    (hhit : orbit c seed t = 2 ^ k) :
    seed + (4 * c + 1) * t ≤ clock :=
  (orbit_linear_growth c seed t).trans (power_hit_le_clock hclock hval hhit)

theorem orbit_one_eq_two_pow_iff {c : ℕ} (hc : 0 < c) (t k : ℕ) :
    orbit c 1 t = 2 ^ k ↔ t = 0 ∧ k = 0 := by
  constructor
  · intro hhit
    have hbound := orbit_power_hit_le_clock (by omega : 0 < t + 1)
      (orbit_one_valuation c t) hhit
    have ht : t = 0 := by nlinarith
    subst t
    have hk : k = 0 := by
      have hv := congrArg (padicValNat 2) hhit
      simpa [orbit, padicValNat.prime_pow] using hv.symm
    exact ⟨rfl, hk⟩
  · rintro ⟨rfl, rfl⟩
    simp [orbit]

/-- All five exact-hit statements follow from their valuation clocks and
elementary growth.  The four nontrivial valuation clocks remain a hypothesis. -/
theorem exactPowerHits_of_valuationClocks (h : ValuationClocksClaim) :
    ExactPowerHitsClaim := by
  intro t k
  have hthree : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have hstep3 : orbit 3 3 1 = 2 ^ 4 := by norm_num [orbit, step, low, hthree]
  refine ⟨orbit_one_eq_two_pow_iff (by decide) t k, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro hx
      have hb := orbit_power_hit_le_clock (by omega : 0 < 3 * t + 2) (h t).2.1 hx
      have ht : t = 0 := by omega
      subst t
      have hk : k = 1 := by
        have hv := congrArg (padicValNat 2) hx
        simpa [orbit, padicValNat.prime_pow] using hv.symm
      exact ⟨rfl, hk⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  · intro hx
    have hb := orbit_power_hit_le_clock (by omega : 0 < 3 * t + 4) (h t).2.2.1 hx
    omega
  · constructor
    · intro hx
      have hb := orbit_power_hit_le_clock (by omega : 0 < 9 * t + 7) (h t).2.2.2.1 hx
      have ht : t = 0 ∨ t = 1 := by omega
      rcases ht with rfl | rfl
      · have hv := congrArg (padicValNat 2) hx
        have hk : k = 0 := by
          simpa [orbit, padicValNat.prime_pow, hthree] using hv.symm
        subst k
        norm_num [orbit] at hx
      · have hv := congrArg (padicValNat 2) hx
        rw [hstep3, padicValNat.prime_pow, padicValNat.prime_pow] at hv
        exact ⟨rfl, hv.symm⟩
    · rintro ⟨rfl, rfl⟩
      exact hstep3
  · intro hx
    have hb := orbit_power_hit_le_clock (by omega : 0 < 9 * t + 11) (h t).2.2.2.2 hx
    omega

/-- Congruence at precision beyond a positive input's valuation determines
the valuation of every other positive representative. -/
theorem valuation_eq_of_modEq {x y K : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : Nat.ModEq (2 ^ K) x y) (hK : padicValNat 2 x < K) :
    padicValNat 2 x = padicValNat 2 y := by
  have hiff (j : ℕ) (hj : j ≤ K) :
      j ≤ padicValNat 2 x ↔ j ≤ padicValNat 2 y := by
    rw [← padicValNat_dvd_iff_le (ne_of_gt hx),
      ← padicValNat_dvd_iff_le (ne_of_gt hy)]
    exact h.dvd_iff (pow_dvd_pow 2 hj)
  have hlower := (hiff (padicValNat 2 x) (by omega)).mp le_rfl
  have hupper : ¬padicValNat 2 x + 1 ≤ padicValNat 2 y := by
    intro hh
    have := (hiff (padicValNat 2 x + 1) (by omega)).mpr hh
    omega
  omega

/-- The low-part function preserves finite binary congruences on positive
inputs.  Positivity excludes the totalized convention `low 0 = 1`. -/
theorem low_modEq_of_modEq {x y K : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : Nat.ModEq (2 ^ K) x y) : Nat.ModEq (2 ^ K) (low x) (low y) := by
  by_cases hK : padicValNat 2 x < K
  · rw [low, low, valuation_eq_of_modEq hx hy h hK]
  · have hxdiv : 2 ^ K ∣ x :=
      (padicValNat_dvd_iff_le (ne_of_gt hx)).mpr (by omega)
    have hydiv := (h.dvd_iff (dvd_refl _)).mp hxdiv
    have hyv := (padicValNat_dvd_iff_le (ne_of_gt hy)).mp hydiv
    have hlx : Nat.ModEq (2 ^ K) (low x) 0 :=
      Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 (by omega))
    have hly : Nat.ModEq (2 ^ K) (low y) 0 :=
      Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 hyv)
    exact hlx.trans hly.symm

theorem step_modEq_of_modEq {x y K : ℕ} (c : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : Nat.ModEq (2 ^ K) x y) : Nat.ModEq (2 ^ K) (step c x) (step c y) := by
  exact (h.add ((low_modEq_of_modEq hx hy h).mul_left (4 * c))).add_right 1

/-- Binary congruence determines the valuation of nonzero signed inputs
whenever the precision exceeds the first input's valuation. -/
theorem signed_valuation_eq_of_modEq {x y : ℤ} {K : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Int.ModEq (2 ^ K) x y) (hK : padicValNat 2 x.natAbs < K) :
    padicValNat 2 x.natAbs = padicValNat 2 y.natAbs := by
  have hiff (j : ℕ) (hj : j ≤ K) :
      j ≤ padicValNat 2 x.natAbs ↔ j ≤ padicValNat 2 y.natAbs := by
    have hd := (h.of_dvd (pow_dvd_pow (2 : ℤ) hj)).dvd_iff
    have hdx : (2 : ℤ) ^ j ∣ x ↔ j ≤ padicValNat 2 x.natAbs := by
      simpa only [Nat.cast_ofNat, hx, false_or, padicValInt] using
        (padicValInt_dvd_iff (p := 2) j x)
    have hdy : (2 : ℤ) ^ j ∣ y ↔ j ≤ padicValNat 2 y.natAbs := by
      simpa only [Nat.cast_ofNat, hy, false_or, padicValInt] using
        (padicValInt_dvd_iff (p := 2) j y)
    exact hdx.symm.trans (hd.trans hdy)
  have hlower := (hiff (padicValNat 2 x.natAbs) (by omega)).mp le_rfl
  have hupper : ¬padicValNat 2 x.natAbs + 1 ≤ padicValNat 2 y.natAbs := by
    intro hh
    have := (hiff (padicValNat 2 x.natAbs + 1) (by omega)).mpr hh
    omega
  omega

/-- Signed low parts preserve binary congruences away from zero. -/
theorem signed_low_modEq_of_modEq {x y : ℤ} {K : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Int.ModEq (2 ^ K) x y) :
    Int.ModEq (2 ^ K) (low x.natAbs : ℤ) (low y.natAbs : ℤ) := by
  by_cases hK : padicValNat 2 x.natAbs < K
  · rw [low, low, signed_valuation_eq_of_modEq hx hy h hK]
  · have hxdiv : (2 : ℤ) ^ K ∣ x :=
      (padicValInt_dvd_iff K x).mpr (Or.inr (by simpa [padicValInt] using (by omega :
        K ≤ padicValNat 2 x.natAbs)))
    have hydiv := h.dvd_iff.mp hxdiv
    have hyv : K ≤ padicValNat 2 y.natAbs := by
      simpa only [hy, false_or, padicValInt] using (padicValInt_dvd_iff K y).mp hydiv
    have hlx : Int.ModEq (2 ^ K) (low x.natAbs : ℤ) 0 := by
      apply Int.modEq_zero_iff_dvd.mpr
      simp only [low, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_dvd_pow (2 : ℤ) (by omega)
    have hly : Int.ModEq (2 ^ K) (low y.natAbs : ℤ) 0 := by
      apply Int.modEq_zero_iff_dvd.mpr
      simp only [low, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_dvd_pow (2 : ℤ) hyv
    exact hlx.trans hly.symm

end RationalClockResearch

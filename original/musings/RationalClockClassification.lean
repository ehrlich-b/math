import RationalClockPhase
import RationalClockConsequences
import RationalClockInteger
import RationalClockShift
import RationalClockBackward

/-!
# Rational-clock classifications

The phase bound and periodic values are combined with signed clock transport
and the common-future relation from the original proposition interface.
-/

namespace RationalClockResearch

theorem exists_reduced_phase {c : ℕ} {theta : ℚ} {seed : ℤ}
    (h : represents c theta seed) (hnon : ∀ z : ℤ, theta ≠ (z : ℚ)) :
    ∃ (j : ℤ) (s : ℤ), -1 < theta + j ∧ theta + j < 0 ∧
      represents c (theta + j) s := by
  let j := -⌈theta⌉
  obtain ⟨s, hs⟩ := represents_int_shift h hnon j
  refine ⟨j, s, ?_, ?_, hs⟩
  · have hh := Int.ceil_lt_add_one theta
    dsimp [j]
    linarith
  · have hh := lt_of_le_of_ne (Int.le_ceil theta) (hnon ⌈theta⌉)
    dsimp [j]
    linarith

/-- A positive seed represented by an integer clock is on the orbit from one. -/
theorem closed_of_integer_clock {c seed : ℕ} (hseed : 0 < seed)
    {z : ℤ} (h : represents c (z : ℚ) (seed : ℤ)) :
    ∃ m : ℕ, seed = closed c m := by
  cases z with
  | ofNat m =>
      refine ⟨m, ?_⟩
      exact_mod_cast represents_seed_unique h (represents_nat c m)
  | negSucc m =>
      have heq : ((Int.negSucc m : ℤ) : ℚ) = -1 - (m : ℚ) := by
        simp only [Int.negSucc_eq]
        push_cast
        ring
      rw [heq] at h
      have hh := represents_neg_one_sub_nat_seed_nonpos h
      omega

/-- Original coefficient-four rigidity, with no denominator restriction. -/
theorem originalMapRigidity : OriginalMapRigidityClaim := by
  intro seed hseed
  constructor
  · rintro ⟨theta, htheta⟩
    by_cases hint : ∃ z : ℤ, theta = (z : ℚ)
    · obtain ⟨z, rfl⟩ := hint
      exact closed_of_integer_clock hseed htheta
    · have hnon : ∀ z : ℤ, theta ≠ (z : ℚ) := by simpa using hint
      obtain ⟨j, s, hlo, hhi, hs⟩ := exists_reduced_phase htheta hnon
      exact False.elim (no_original_integral_phase hlo hhi hs)
  · rintro ⟨m, rfl⟩
    exact hasRationalClock_closed 1 m

theorem sameFuture_of_shifted_clock {c a b : ℕ} {theta eta : ℚ}
    (ha : represents c theta (a : ℤ)) (hb : represents c eta (b : ℤ))
    (ha_pos : 0 < a) (hb_pos : 0 < b) (j : ℤ) (hj : theta + j = eta) :
    sameFuture c a b := by
  apply (sameFuture_iff_clock_shifts ha hb ha_pos hb_pos).mpr
  cases j with
  | ofNat n => exact ⟨n, 0, by simpa using hj⟩
  | negSucc n =>
      refine ⟨0, n + 1, ?_⟩
      simp only [Int.negSucc_eq] at hj
      push_cast at hj ⊢
      linarith

/-- Every positive coefficient-twelve seed with a rational clock belongs to
one of the five explicit common-future classes. -/
theorem fiveClasses_forward {seed : ℕ} (hseed : 0 < seed)
    (h : hasRationalClock 3 seed) :
    sameFuture 3 seed 1 ∨ sameFuture 3 seed 2 ∨ sameFuture 3 seed 12 ∨
      sameFuture 3 seed 3 ∨ sameFuture 3 seed 23 := by
  obtain ⟨theta, htheta⟩ := h
  by_cases hint : ∃ z : ℤ, theta = (z : ℚ)
  · obtain ⟨z, rfl⟩ := hint
    obtain ⟨m, hm⟩ := closed_of_integer_clock hseed htheta
    apply Or.inl
    exact ⟨0, m, by simpa [orbit, orbit_one_eq_closed] using hm⟩
  · have hnon : ∀ z : ℤ, theta ≠ (z : ℚ) := by simpa using hint
    obtain ⟨j, s, hlo, hhi, hs⟩ := exists_reduced_phase htheta hnon
    have hphase := (coefficientTwelvePhase (theta + j) s hlo hhi).mp hs
    rcases hphase with ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
    · exact Or.inr (Or.inl
        (sameFuture_of_shifted_clock htheta represents_three_neg_one_third
          hseed (by decide) j heq))
    · apply Or.inr ∘ Or.inr ∘ Or.inl
      apply sameFuture_of_shifted_clock htheta represents_three_one_third
        hseed (by decide) (j + 1)
      push_cast
      linarith
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (sameFuture_of_shifted_clock htheta represents_three_neg_two_ninths
          hseed (by decide) j heq))))
    · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
      apply sameFuture_of_shifted_clock htheta represents_three_two_ninths
        hseed (by decide) (j + 1)
      push_cast
      linarith

/-- Exactly five rational-clock positive orbit classes, with no denominator
cutoff and with pairwise distinct common futures. -/
theorem fiveClasses : FiveClassesClaim := by
  refine ⟨?_, five_representatives_pairwise⟩
  intro seed hseed
  constructor
  · exact fiveClasses_forward hseed
  · intro hf
    rcases hf with hf | hf | hf | hf | hf
    · exact hasRationalClock_of_sameFuture hseed (by decide) hf
        ⟨0, represents_zero 3⟩
    · exact hasRationalClock_of_sameFuture hseed (by decide) hf
        ⟨-(1 : ℚ) / 3, represents_three_neg_one_third⟩
    · exact hasRationalClock_of_sameFuture hseed (by decide) hf
        ⟨(1 : ℚ) / 3, represents_three_one_third⟩
    · exact hasRationalClock_of_sameFuture hseed (by decide) hf
        ⟨-(2 : ℚ) / 9, represents_three_neg_two_ninths⟩
    · exact hasRationalClock_of_sameFuture hseed (by decide) hf
        ⟨(2 : ℚ) / 9, represents_three_two_ninths⟩

end RationalClockResearch

import RationalClockDynamics
import RationalClockPeriodic

/-!
# Explicit valuation clocks and exact power-of-two hits

The finite periodic evaluations and clock transport identify the valuation
clock of each of the five positive coefficient-twelve representatives.
The resulting exact-hit classification uses the previously proved growth
bound; it does not require completeness of the rational-clock classification.
-/

namespace RationalClockResearch

theorem represents_three_one_third : represents 3 ((1 : ℚ) / 3) 12 := by
  have h := represents_add_one represents_three_neg_two_thirds (by norm_num)
  norm_num [low] at h
  exact h

theorem represents_three_two_ninths : represents 3 ((2 : ℚ) / 9) 23 := by
  have h := represents_add_one represents_three_neg_seven_ninths (by norm_num)
  norm_num [low] at h
  exact h

/-- Express the valuation clock as an ordinary positive affine numerator. -/
theorem orbit_valuation_of_represents {c seed A B : ℕ} {theta : ℚ}
    (h : represents c theta (seed : ℤ)) (hseed : 0 < seed)
    (hA : theta.den = A) (hB : theta.num + (theta.den : ℤ) = B)
    (hBpos : 0 < B) (t : ℕ) :
    padicValNat 2 (orbit c seed t) = padicValNat 2 (A * t + B) := by
  have hnum : (theta + t).num + ((theta + t).den : ℤ) = (A * t + B : ℕ) := by
    rw [rat_add_nat_num, Rat.add_natCast_den, hA]
    rw [hA] at hB
    push_cast
    linear_combination hB
  have hpos : 0 < (theta + t).num + ((theta + t).den : ℤ) := by
    rw [hnum]
    exact_mod_cast (show 0 < A * t + B by omega)
  have hv := represents_valuation (represents_orbit h hseed t) (orbit_pos hseed) hpos
  rw [hnum] at hv
  simpa only [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_natCast] using hv

/-- All five valuation clocks from the proposition interface are verified. -/
theorem valuationClocks : ValuationClocksClaim := by
  intro t
  refine ⟨orbit_one_valuation 3 t, ?_, ?_, ?_, ?_⟩
  · exact orbit_valuation_of_represents (A := 3) (B := 2)
      represents_three_neg_one_third (by decide) (by norm_num) (by norm_num) (by decide) t
  · exact orbit_valuation_of_represents (A := 3) (B := 4)
      represents_three_one_third (by decide) (by norm_num) (by norm_num) (by decide) t
  · exact orbit_valuation_of_represents (A := 9) (B := 7)
      represents_three_neg_two_ninths (by decide) (by norm_num) (by norm_num) (by decide) t
  · exact orbit_valuation_of_represents (A := 9) (B := 11)
      represents_three_two_ninths (by decide) (by norm_num) (by norm_num) (by decide) t

/-- The exact power-of-two hits for all five positive representatives. -/
theorem exactPowerHits : ExactPowerHitsClaim :=
  exactPowerHits_of_valuationClocks valuationClocks

/-- Positive represented seeds have a common future exactly when their
rational clocks agree after nonnegative integer shifts. -/
theorem sameFuture_iff_clock_shifts {c a b : ℕ} {theta eta : ℚ}
    (ha : represents c theta (a : ℤ)) (hb : represents c eta (b : ℤ))
    (ha_pos : 0 < a) (hb_pos : 0 < b) :
    sameFuture c a b ↔ ∃ m n : ℕ, theta + m = eta + n := by
  constructor
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    have ham := represents_orbit ha ha_pos m
    rw [hmn] at ham
    exact represents_clock_unique ham (represents_orbit hb hb_pos n)
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    have ham := represents_orbit ha ha_pos m
    rw [hmn] at ham
    exact_mod_cast represents_seed_unique ham (represents_orbit hb hb_pos n)

private def representativeClockNumerator : ℕ → ℤ
  | 1 => 0
  | 2 => -3
  | 12 => 3
  | 3 => -2
  | 23 => 2
  | _ => 0

private theorem representative_clock (a : ℕ) (ha : a ∈ ([1, 2, 12, 3, 23] : List ℕ)) :
    represents 3 ((representativeClockNumerator a : ℚ) / 9) (a : ℤ) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · norm_num [representativeClockNumerator]
  · convert represents_three_neg_one_third using 1 <;> norm_num [representativeClockNumerator]
  · convert represents_three_one_third using 1 <;> norm_num [representativeClockNumerator]
  · convert represents_three_neg_two_ninths using 1 <;> norm_num [representativeClockNumerator]
  · convert represents_three_two_ninths using 1 <;> norm_num [representativeClockNumerator]

private theorem representative_clock_bounds (a : ℕ)
    (ha : a ∈ ([1, 2, 12, 3, 23] : List ℕ)) :
    -4 ≤ representativeClockNumerator a ∧ representativeClockNumerator a ≤ 4 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> norm_num [representativeClockNumerator]

private theorem representative_clock_injective {a b : ℕ}
    (ha : a ∈ ([1, 2, 12, 3, 23] : List ℕ))
    (hb : b ∈ ([1, 2, 12, 3, 23] : List ℕ))
    (h : representativeClockNumerator a = representativeClockNumerator b) : a = b := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [representativeClockNumerator]

/-- The five explicitly represented positive orbits have distinct common
futures.  This proves the disjointness conjunct of `FiveClassesClaim`. -/
theorem five_representatives_pairwise :
    ∀ a ∈ ([1, 2, 12, 3, 23] : List ℕ),
      ∀ b ∈ ([1, 2, 12, 3, 23] : List ℕ), sameFuture 3 a b → a = b := by
  intro a ha b hb hfuture
  have hapos : 0 < a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    omega
  have hbpos : 0 < b := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    omega
  obtain ⟨m, n, hmn⟩ :=
    (sameFuture_iff_clock_shifts (representative_clock a ha) (representative_clock b hb)
      hapos hbpos).mp hfuture
  have hrat : (representativeClockNumerator a : ℚ) + 9 * (m : ℚ) =
      (representativeClockNumerator b : ℚ) + 9 * (n : ℚ) := by linarith
  have hint : representativeClockNumerator a + 9 * (m : ℤ) =
      representativeClockNumerator b + 9 * (n : ℤ) := by exact_mod_cast hrat
  have habounds := representative_clock_bounds a ha
  have hbbounds := representative_clock_bounds b hb
  apply representative_clock_injective ha hb
  omega

end RationalClockResearch

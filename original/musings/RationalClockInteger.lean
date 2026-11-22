import RationalClockRepresentation

/-!
# Integer clocks and finite binary complementation

Complementation at a fixed binary precision identifies the negative integer
clock values without extending the natural low-part function to zero.
-/

namespace RationalClockResearch

/-- Complementing every bit below precision `K` complements the clock value
against the all-ones clock value. -/
theorem closed_complement (c K m : ℕ) (hm : m < 2 ^ K) :
    closed c (2 ^ K - 1 - m) + closed c m = closed c (2 ^ K - 1) + 1 := by
  induction K generalizing m with
  | zero =>
      have hm0 : m = 0 := by simpa using hm
      subst m
      simp
  | succ K ih =>
      have hpow : 1 ≤ 2 ^ K := Nat.one_le_pow K 2 (by omega)
      have hone : 2 ^ (K + 1) - 1 = 2 * (2 ^ K - 1) + 1 := by
        rw [pow_succ]
        omega
      rcases Nat.even_or_odd m with heven | hodd
      · obtain ⟨b, rfl⟩ := heven
        rw [show b + b = 2 * b by omega] at hm ⊢
        have hb : b < 2 ^ K := by rw [pow_succ] at hm; omega
        have hi := ih b hb
        have hs : (2 ^ K - 1 - b) + b = 2 ^ K - 1 := by omega
        have hc := congrArg (fun n : ℕ => 4 * c * n) hs
        have hcomp : 2 ^ (K + 1) - 1 - 2 * b =
            2 * (2 ^ K - 1 - b) + 1 := by rw [pow_succ]; omega
        rw [hcomp, hone, closed_two_mul_add_one, closed_two_mul_add_one]
        have hbit := closed_two_mul_succ c b
        nlinarith only [hi, hc, hbit]
      · obtain ⟨b, rfl⟩ := hodd
        have hb : b < 2 ^ K := by rw [pow_succ] at hm; omega
        have hi := ih b hb
        have hs : (2 ^ K - 1 - b) + b = 2 ^ K - 1 := by omega
        have hc := congrArg (fun n : ℕ => 4 * c * n) hs
        have hcomp : 2 ^ (K + 1) - 1 - (2 * b + 1) =
            2 * (2 ^ K - 1 - b) := by rw [pow_succ]; omega
        rw [hcomp, hone, closed_two_mul_add_one, closed_two_mul_add_one]
        have hbit := closed_two_mul_succ c (2 ^ K - 1 - b)
        nlinarith only [hi, hc, hbit]

/-- Every negative integer clock has its exact complementary integer value. -/
theorem represents_neg_one_sub_nat (c m : ℕ) :
    represents c (-1 - (m : ℚ)) (1 - (closed c m : ℤ)) := by
  have htheta : -1 - (m : ℚ) = ((-1 - (m : ℤ) : ℤ) : ℚ) := by push_cast; rfl
  rw [htheta]
  refine ⟨by simp, ?_⟩
  intro K a ha
  simp only [Rat.den_intCast, Rat.num_intCast, Nat.cast_one, one_mul] at ha
  let J := K + m
  let q := 2 ^ J - 1 - m
  have hKJ : K ≤ J := by dsimp [J]; omega
  have hmJ : m < 2 ^ J :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by dsimp [J]; omega))
  have hq : q + m + 1 = 2 ^ J := by dsimp [q]; omega
  have hqZ := congrArg (fun n : ℕ => (n : ℤ)) hq
  push_cast at hqZ
  have hdvd : (2 : ℤ) ^ K ∣ (2 : ℤ) ^ J := pow_dvd_pow 2 hKJ
  have hindex : Int.ModEq (2 ^ K) (q : ℤ) (-1 - (m : ℤ)) := by
    apply Int.modEq_iff_dvd.mpr
    rw [show -1 - (m : ℤ) - (q : ℤ) = -((2 : ℤ) ^ J) by linarith only [hqZ]]
    exact dvd_neg.mpr hdvd
  have hcomp := closed_complement c J m hmJ
  rw [closed_two_pow_sub_one] at hcomp
  have hcompZ := congrArg (fun n : ℕ => (n : ℤ)) hcomp
  push_cast at hcompZ
  have hvalue : Int.ModEq (2 ^ K) (closed c q : ℤ) (1 - (closed c m : ℤ)) := by
    apply Int.modEq_iff_dvd.mpr
    have hd := dvd_mul_of_dvd_left hdvd (1 + 2 * (c : ℤ) * J)
    rw [show 1 - (closed c m : ℤ) - (closed c q : ℤ) =
      -((2 : ℤ) ^ J * (1 + 2 * (c : ℤ) * J)) by linarith only [hcompZ]]
    exact dvd_neg.mpr hd
  exact ((closed_modEq_iff c K a q).mpr (ha.trans hindex.symm)).trans hvalue

/-- In particular, an integer clock below zero cannot represent a positive seed. -/
theorem represents_neg_one_sub_nat_seed_nonpos {c m : ℕ} {seed : ℤ}
    (h : represents c (-1 - (m : ℚ)) seed) : seed ≤ 0 := by
  have heq := represents_seed_unique h (represents_neg_one_sub_nat c m)
  have hclosed : 1 ≤ closed c m := by simp only [closed]; omega
  rw [heq]
  omega

end RationalClockResearch

import RationalClockBasic

/-!
# The finite binary-clock isometry

The auxiliary odd-linear family is closed under deleting the lowest binary
digit. This gives an induction on precision without introducing infinite sums.
-/

namespace RationalClockResearch

private def clockLinear (c a n : ℕ) : ℕ :=
  (2 * a + 1) * n + 4 * c * rulerSum n

private theorem clockLinear_two_mul (c a n : ℕ) :
    clockLinear c a (2 * n) = 2 * clockLinear c (a + c) n := by
  simp only [clockLinear, rulerSum_two_mul]
  ring

private theorem clockLinear_two_mul_add_one (c a n : ℕ) :
    clockLinear c a (2 * n + 1) =
      2 * clockLinear c (a + c) n + (2 * a + 1 + 4 * c) := by
  simp only [clockLinear, rulerSum_two_mul_add_one]
  ring

private theorem clockLinear_mod_two (c a n : ℕ) :
    clockLinear c a n % 2 = n % 2 := by
  simp [clockLinear, Nat.add_mod, Nat.mul_mod]

private theorem modEq_pow_two_parity {K m n : ℕ}
    (h : Nat.ModEq (2 ^ (K + 1)) m n) : m % 2 = n % 2 := by
  exact h.of_dvd (dvd_pow_self 2 (Nat.succ_ne_zero K))

private theorem clockLinear_modEq_iff (c K a m n : ℕ) :
    Nat.ModEq (2 ^ K) (clockLinear c a m) (clockLinear c a n) ↔
      Nat.ModEq (2 ^ K) m n := by
  induction K generalizing a m n with
  | zero => simp only [pow_zero, Nat.ModEq, Nat.mod_one]
  | succ K ih =>
      by_cases hp : m % 2 = n % 2
      · obtain ⟨q, hq⟩ : ∃ q, m = 2 * q + m % 2 := ⟨m / 2, by omega⟩
        obtain ⟨r, hr⟩ : ∃ r, n = 2 * r + m % 2 := ⟨n / 2, by omega⟩
        have hb : m % 2 = 0 ∨ m % 2 = 1 := by omega
        rcases hb with hb | hb
        · simp only [hb, add_zero] at hq hr
          rw [hq, hr, clockLinear_two_mul, clockLinear_two_mul, pow_succ']
          simp only [Nat.ModEq.mul_left_cancel_iff' (by decide : 2 ≠ 0)]
          exact ih (a + c) q r
        · rw [hb] at hq hr
          rw [hq, hr, clockLinear_two_mul_add_one, clockLinear_two_mul_add_one,
            pow_succ']
          simp only [Nat.ModEq.add_iff_right (Nat.ModEq.refl _),
            Nat.ModEq.mul_left_cancel_iff' (by decide : 2 ≠ 0)]
          exact ih (a + c) q r
      · constructor
        · intro h
          have hparity := modEq_pow_two_parity h
          rw [clockLinear_mod_two, clockLinear_mod_two] at hparity
          exact False.elim (hp hparity)
        · intro h
          exact False.elim (hp (modEq_pow_two_parity h))

/-- The closed clock preserves and reflects every finite binary congruence. -/
theorem closed_natModEq_iff (c K m n : ℕ) :
    Nat.ModEq (2 ^ K) (closed c m) (closed c n) ↔ Nat.ModEq (2 ^ K) m n := by
  have hm : closed c m = clockLinear c 0 m + 1 := by simp [closed, clockLinear]; omega
  have hn : closed c n = clockLinear c 0 n + 1 := by simp [closed, clockLinear]; omega
  rw [hm, hn, Nat.ModEq.add_iff_right (Nat.ModEq.refl 1)]
  exact clockLinear_modEq_iff c K 0 m n

/-- Integer-congruence interface for the finite binary-clock isometry. -/
theorem closed_modEq_iff (c K m n : ℕ) :
    Int.ModEq (2 ^ K) (closed c m : ℤ) (closed c n : ℤ) ↔
      Int.ModEq (2 ^ K) (m : ℤ) (n : ℤ) := by
  norm_cast
  exact closed_natModEq_iff c K m n

/-! ## Finite inverse clocks and compatibility -/

/-- The clock map on the residues at a fixed binary precision. -/
def closedResidue (c K : ℕ) (m : ZMod (2 ^ K)) : ZMod (2 ^ K) :=
  (closed c m.val : ZMod (2 ^ K))

theorem closedResidue_injective (c K : ℕ) : Function.Injective (closedResidue c K) := by
  have : NeZero (2 ^ K) := ⟨pow_ne_zero _ (by decide)⟩
  intro m n h
  have hm : Nat.ModEq (2 ^ K) (closed c m.val) (closed c n.val) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have hi := (closed_natModEq_iff c K m.val n.val).mp hm
  exact ZMod.val_injective _ (hi.eq_of_lt_of_lt m.val_lt n.val_lt)

/-- Every finite binary clock map is a permutation. -/
theorem closedResidue_bijective (c K : ℕ) : Function.Bijective (closedResidue c K) := by
  have : NeZero (2 ^ K) := ⟨pow_ne_zero _ (by decide)⟩
  exact ⟨closedResidue_injective c K,
    Finite.surjective_of_injective (closedResidue_injective c K)⟩

/-- A permutation formulation of the finite clock, including its inverse. -/
noncomputable def closedResidueEquiv (c K : ℕ) : ZMod (2 ^ K) ≃ ZMod (2 ^ K) :=
  Equiv.ofBijective (closedResidue c K) (closedResidue_bijective c K)

/-- The unique index residue representing an arbitrary integer seed. -/
noncomputable def finiteClock (c K : ℕ) (seed : ℤ) : ZMod (2 ^ K) :=
  (closedResidueEquiv c K).symm (seed : ZMod (2 ^ K))

theorem finiteClock_spec (c K : ℕ) (seed : ℤ) :
    Int.ModEq (2 ^ K) (closed c (finiteClock c K seed).val : ℤ) seed := by
  change Int.ModEq ((2 ^ K : ℕ) : ℤ) _ _
  rw [← ZMod.intCast_eq_intCast_iff]
  simp only [Int.cast_natCast]
  exact (closedResidueEquiv c K).apply_symm_apply (seed : ZMod (2 ^ K))

/-- Any index satisfying the seed congruence has the inverse clock's residue. -/
theorem finiteClock_unique (c K m : ℕ) (seed : ℤ)
    (h : Int.ModEq (2 ^ K) (closed c m : ℤ) seed) :
    Int.ModEq (2 ^ K) (m : ℤ) ((finiteClock c K seed).val : ℤ) := by
  exact (closed_modEq_iff c K m _).mp (h.trans (finiteClock_spec c K seed).symm)

/-- Increasing precision does not change any previously recovered clock bits. -/
theorem finiteClock_compatible (c K L : ℕ) (seed : ℤ) (hKL : K ≤ L) :
    Int.ModEq (2 ^ K) ((finiteClock c L seed).val : ℤ)
      ((finiteClock c K seed).val : ℤ) := by
  apply finiteClock_unique
  exact (finiteClock_spec c L seed).of_dvd (pow_dvd_pow 2 hKL)

end RationalClockResearch

import RationalClockConsequences

/-!
# Reflecting finite congruences and rational clocks backwards

The factor four in the low-part correction gives a direct induction on
precision: once inputs agree modulo `2^K`, their correction terms agree modulo
`2^(K+1)`.  Thus the positive step map reflects congruences as well as
preserving them.  Rational-clock existence is consequently invariant under
having a common positive future.
-/

namespace RationalClockResearch

theorem step_natModEq_iff (c K a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nat.ModEq (2 ^ K) (step c a) (step c b) ↔ Nat.ModEq (2 ^ K) a b := by
  induction K with
  | zero => simp only [pow_zero, Nat.ModEq, Nat.mod_one]
  | succ K ih =>
      constructor
      · intro hs
        have hprev := ih.mp (hs.of_dvd (pow_dvd_pow 2 (Nat.le_succ K)))
        have hl := low_modEq_of_modEq ha hb hprev
        have hcorrection : Nat.ModEq (2 ^ (K + 1)) (4 * c * low a) (4 * c * low b) := by
          rw [pow_succ']
          convert (hl.mul_left' 2).mul_left (2 * c) using 1 <;> ring
        have hs' : Nat.ModEq (2 ^ (K + 1)) (a + 4 * c * low a) (b + 4 * c * low b) :=
          Nat.ModEq.add_right_cancel' 1 hs
        exact hcorrection.add_right_cancel hs'
      · exact step_modEq_of_modEq c ha hb

/-- Integer-congruence interface for reflection by the positive step map. -/
theorem step_modEq_iff (c K a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Int.ModEq (2 ^ K) (step c a : ℤ) (step c b : ℤ) ↔
      Int.ModEq (2 ^ K) (a : ℤ) (b : ℤ) := by
  norm_cast
  exact step_natModEq_iff c K a b ha hb

/-- Pull a clock back one tick from a known positive predecessor. -/
theorem represents_of_step {c seed : ℕ} {theta : ℚ} (hseed : 0 < seed)
    (h : represents c (theta + 1) (step c seed : ℤ)) :
    represents c theta (seed : ℤ) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro K m hm
  have hnum : (theta + 1).num = theta.num + (theta.den : ℤ) := by
    simpa using rat_add_nat_num theta 1
  have hi : Int.ModEq (2 ^ K) (((theta + 1).den : ℤ) * ((m + 1 : ℕ) : ℤ))
      (theta + 1).num := by
    rw [hnum, Rat.add_ofNat_den]
    convert hm.add_right (theta.den : ℤ) using 1
    push_cast
    ring
  have hs := h.2 K (m + 1) hi
  rw [closed_succ_eq_step_of_low_eq c m (closed_low c m)] at hs
  exact (step_modEq_iff c K (closed c m) seed (closed_pos c m) hseed).mp hs

theorem hasRationalClock_of_step {c seed : ℕ} (hseed : 0 < seed)
    (h : hasRationalClock c (step c seed)) : hasRationalClock c seed := by
  obtain ⟨theta, htheta⟩ := h
  refine ⟨theta - 1, represents_of_step hseed ?_⟩
  simpa using htheta

theorem hasRationalClock_of_orbit {c seed t : ℕ} (hseed : 0 < seed)
    (h : hasRationalClock c (orbit c seed t)) : hasRationalClock c seed := by
  induction t with
  | zero => simpa [orbit] using h
  | succ t ih =>
      apply ih
      exact hasRationalClock_of_step (orbit_pos hseed) (by simpa [orbit] using h)

theorem hasRationalClock_of_sameFuture {c a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hfuture : sameFuture c a b) (h : hasRationalClock c b) : hasRationalClock c a := by
  obtain ⟨m, n, hmn⟩ := hfuture
  apply hasRationalClock_of_orbit (t := m) ha
  rw [hmn]
  exact hasRationalClock_orbit h hb n

theorem hasRationalClock_sameFuture_iff {c a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hfuture : sameFuture c a b) : hasRationalClock c a ↔ hasRationalClock c b := by
  have hsymm : sameFuture c b a := by
    obtain ⟨m, n, hmn⟩ := hfuture
    exact ⟨n, m, hmn.symm⟩
  exact ⟨hasRationalClock_of_sameFuture hb ha hsymm,
    hasRationalClock_of_sameFuture ha hb hfuture⟩

end RationalClockResearch

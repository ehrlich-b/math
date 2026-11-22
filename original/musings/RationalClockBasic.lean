import RationalClockStatements

/-!
# Verified elementary layer for the rational-clock project

This file proves the recurrence bookkeeping that does not depend on the main
binary-clock isometry.  In particular, it records the totalized value of
`low 0`, proves positivity and growth of the natural-number dynamics, and
isolates the valuation identity needed to identify `closed` with an orbit.
-/

namespace RationalClockResearch

@[simp] theorem low_zero : low 0 = 1 := by
  simp [low]

theorem low_pos (n : ℕ) : 0 < low n := by
  simp [low]

@[simp] theorem low_two_mul_add_one (n : ℕ) : low (2 * n + 1) = 1 := by
  rw [low, padicValNat.eq_zero_of_not_dvd]
  · simp
  · omega

theorem low_two_mul_succ (n : ℕ) :
    low (2 * (n + 1)) = 2 * low (n + 1) := by
  rw [low, padicValNat_base_mul (by omega) (Nat.succ_ne_zero n)]
  simp [low, pow_succ, Nat.mul_comm]

@[simp] theorem rulerSum_succ (n : ℕ) :
    rulerSum (n + 1) = rulerSum n + low (n + 1) := by
  rfl

theorem rulerSum_two_mul : ∀ n : ℕ,
    rulerSum (2 * n) = n + 2 * rulerSum n := by
  intro n
  induction n with
  | zero => simp [rulerSum]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      rw [rulerSum_succ]
      rw [show 2 * n + 1 = 2 * n + 1 by rfl]
      rw [rulerSum_succ, ih, low_two_mul_add_one]
      rw [show (2 * n + 1) + 1 = 2 * (n + 1) by omega]
      rw [low_two_mul_succ, rulerSum_succ]
      omega

theorem rulerSum_two_mul_add_one (n : ℕ) :
    rulerSum (2 * n + 1) = n + 2 * rulerSum n + 1 := by
  rw [rulerSum_succ, rulerSum_two_mul, low_two_mul_add_one]

@[simp] theorem closed_zero (c : ℕ) : closed c 0 = 1 := by
  simp [closed, rulerSum]

theorem closed_succ (c n : ℕ) :
    closed c (n + 1) = closed c n + 1 + 4 * c * low (n + 1) := by
  simp only [closed, rulerSum, Nat.mul_add]
  ring

theorem closed_two_mul_succ (c n : ℕ) :
    closed c (2 * n) + 1 = 2 * closed c n + 4 * c * n := by
  simp only [closed, rulerSum_two_mul]
  ring

theorem closed_two_mul_add_one (c n : ℕ) :
    closed c (2 * n + 1) = 2 * closed c n + 4 * c * n + 4 * c := by
  simp only [closed, rulerSum_two_mul_add_one]
  ring

theorem closed_two_mul_odd (c n : ℕ) : Odd (closed c (2 * n)) := by
  refine ⟨n + 2 * c * (n + 2 * rulerSum n), ?_⟩
  simp only [closed, rulerSum_two_mul]
  ring

theorem closed_two_mul_add_one_even (c n : ℕ) :
    Even (closed c (2 * n + 1)) := by
  refine ⟨closed c n + 2 * c * n + 2 * c, ?_⟩
  rw [closed_two_mul_add_one]
  ring

theorem step_gt (c x : ℕ) : x < step c x := by
  simp only [step]
  omega

theorem step_pos (c x : ℕ) : 0 < step c x :=
  Nat.zero_lt_of_lt (step_gt c x)

theorem orbit_pos {c seed t : ℕ} (hseed : 0 < seed) :
    0 < orbit c seed t := by
  induction t with
  | zero => simpa [orbit] using hseed
  | succ t ih => simpa [orbit] using step_pos c (orbit c seed t)

theorem orbit_add_le {c seed : ℕ} (t : ℕ) :
    seed + t ≤ orbit c seed t := by
  induction t with
  | zero => simp [orbit]
  | succ t ih =>
      rw [orbit]
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (step_gt c (orbit c seed t)))

theorem orbit_strictMono (c seed : ℕ) : StrictMono (orbit c seed) := by
  apply strictMono_nat_of_lt_succ
  intro t
  simpa [orbit] using step_gt c (orbit c seed t)

theorem closed_succ_eq_step_of_low_eq (c n : ℕ)
    (h : low (closed c n) = low (n + 1)) :
    closed c (n + 1) = step c (closed c n) := by
  rw [closed_succ, step, h]
  omega

/-- Once the clock valuation identity is known, the closed form is the orbit. -/
theorem orbit_one_eq_closed_of_low_eq (c : ℕ)
    (h : ∀ n : ℕ, low (closed c n) = low (n + 1)) :
    ∀ t : ℕ, orbit c 1 t = closed c t := by
  intro t
  induction t with
  | zero => simp [orbit]
  | succ t ih =>
      rw [orbit, ih, ← closed_succ_eq_step_of_low_eq c t (h t)]

/-! ## The finite-residue clock definition is nonvacuous -/

/-- An odd rational denominator has an index representative modulo every
power of two.  This closes the vacuity trap called out in the handoff. -/
theorem exists_index_mod (theta : ℚ) (hodd : Odd theta.den) (K : ℕ) :
    ∃ m : ℕ, Int.ModEq (2 ^ K) ((theta.den : ℤ) * (m : ℤ)) theta.num := by
  let N : ℕ := 2 ^ K
  have hN : N ≠ 0 := by simp [N]
  have hNZ : NeZero N := ⟨hN⟩
  have hcop : theta.den.Coprime N := by
    exact hodd.coprime_two_right.pow_right K
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime theta.den hcop
  let z : ZMod N := (u⁻¹ : (ZMod N)ˣ) * (theta.num : ZMod N)
  refine ⟨z.val, ?_⟩
  change Int.ModEq (N : ℤ) ((theta.den : ℤ) * (z.val : ℤ)) theta.num
  rw [← ZMod.intCast_eq_intCast_iff]
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [@ZMod.natCast_zmod_val N hNZ z]
  change (u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) * (theta.num : ZMod N)) = _
  rw [← mul_assoc, Units.mul_inv, one_mul]

/-- A fixed rational clock cannot `represent` two different integer seeds.
The proof uses an actual index representative at a modulus larger than their
difference; it does not rely on a potentially vacuous implication. -/
theorem represents_seed_unique {c : ℕ} {theta : ℚ} {seed₁ seed₂ : ℤ}
    (h₁ : represents c theta seed₁) (h₂ : represents c theta seed₂) :
    seed₁ = seed₂ := by
  let K := (seed₂ - seed₁).natAbs
  obtain ⟨m, hm⟩ := exists_index_mod theta h₁.1 K
  have hc₁ := h₁.2 K m hm
  have hc₂ := h₂.2 K m hm
  have hs : Int.ModEq (2 ^ K) seed₁ seed₂ := hc₁.symm.trans hc₂
  have hdvd : ((2 ^ K : ℕ) : ℤ) ∣ seed₂ - seed₁ := hs.dvd
  have hlt : (seed₂ - seed₁).natAbs < Int.natAbs ((2 ^ K : ℕ) : ℤ) := by
    simp only [Int.natAbs_natCast]
    exact Nat.lt_two_pow_self
  have hz : seed₂ - seed₁ = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt
  omega

end RationalClockResearch

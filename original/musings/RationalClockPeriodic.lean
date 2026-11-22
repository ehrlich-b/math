import RationalClockIsometry

/-!
# Finite repeated-block evaluation of rational clocks

The results here use finite natural-number indices and integer identities only.
In particular, periodic evaluation does not identify a real infinite sum with
a 2-adic infinite sum.
-/

namespace RationalClockResearch

/-- Concatenating an `L`-bit block to an index gives an affine formula for
the clock map.  The added power of two avoids natural-number subtraction. -/
theorem closed_concat (c L n B : ℕ) (hB : B < 2 ^ L) :
    closed c (2 ^ L * n + B) + 2 ^ L =
      closed c B + 2 ^ L * closed c n + 2 * c * L * 2 ^ L * n := by
  induction L generalizing B with
  | zero =>
      have hB0 : B = 0 := by simpa using hB
      subst B
      simp [Nat.add_comm]
  | succ L ih =>
      rcases Nat.even_or_odd B with hEven | hOdd
      · obtain ⟨b, rfl⟩ := hEven
        have hb : b < 2 ^ L := by
          rw [pow_succ] at hB
          omega
        have hi := ih b hb
        have h₁ := closed_two_mul_succ c (2 ^ L * n + b)
        have h₂ := closed_two_mul_succ c b
        rw [show b + b = 2 * b by omega]
        rw [show 2 ^ (L + 1) * n + 2 * b = 2 * (2 ^ L * n + b) by
          rw [pow_succ]; ring]
        rw [pow_succ]
        nlinarith only [hi, h₁, h₂]
      · obtain ⟨b, rfl⟩ := hOdd
        have hb : b < 2 ^ L := by
          rw [pow_succ] at hB
          omega
        have hi := ih b hb
        rw [show 2 ^ (L + 1) * n + (2 * b + 1) =
          2 * (2 ^ L * n + b) + 1 by rw [pow_succ]; ring]
        rw [closed_two_mul_add_one, closed_two_mul_add_one, pow_succ]
        nlinarith only [hi]

/-- The natural index obtained by repeating one `L`-bit block `r` times. -/
def repeatedBlock (L B : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => 2 ^ L * repeatedBlock L B r + B

/-- The geometric identity uses integers so that it also includes `r = 0`.
It does not require division or a nonzero denominator. -/
theorem repeatedBlock_geometric (L B r : ℕ) :
    ((2 : ℤ) ^ L - 1) * (repeatedBlock L B r : ℤ) =
      (B : ℤ) * ((2 : ℤ) ^ (L * r) - 1) := by
  induction r with
  | zero => simp [repeatedBlock]
  | succ r ih =>
      simp only [repeatedBlock, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [Nat.mul_succ, pow_add]
      linear_combination (2 : ℤ) ^ L * ih

/-- The numerator of the exact periodic-phase value.  `closed c B - 1` is
the note's block weight `A`, avoiding a separate binary-digit-sum definition. -/
def periodicNumerator (c L B : ℕ) : ℤ :=
  ((2 : ℤ) ^ L - 1) ^ 2 - ((closed c B : ℤ) - 1) * ((2 : ℤ) ^ L - 1) +
    2 * c * L * B * (2 : ℤ) ^ L

/-- Exact finite repeated-block evaluation (equation (4) of the note),
including the empty block repetition. -/
theorem closed_repeatedBlock (c L B r : ℕ) (hB : B < 2 ^ L) :
    ((2 : ℤ) ^ L - 1) ^ 2 * (closed c (repeatedBlock L B r) : ℤ) =
      periodicNumerator c L B + (2 : ℤ) ^ (L * r) *
        (((closed c B : ℤ) - 1) * ((2 : ℤ) ^ L - 1) +
          2 * c * L * B * (((r : ℤ) - 1) * (2 : ℤ) ^ L - r)) := by
  induction r with
  | zero => simp [repeatedBlock, periodicNumerator]; ring
  | succ r ih =>
      have hrec := closed_concat c L (repeatedBlock L B r) B hB
      have hrecZ := congrArg (fun n : ℕ => (n : ℤ)) hrec
      push_cast at hrecZ
      have hgeom := repeatedBlock_geometric L B r
      simp only [repeatedBlock, Nat.cast_add, Nat.cast_one]
      rw [Nat.mul_succ, pow_add]
      unfold periodicNumerator at ih ⊢
      linear_combination ((2 : ℤ) ^ L - 1) ^ 2 * hrecZ +
        (2 : ℤ) ^ L * ih +
        (2 * (c : ℤ) * L * (2 : ℤ) ^ L * ((2 : ℤ) ^ L - 1)) * hgeom

private theorem modEq_cancel_odd {K : ℕ} {a b u : ℤ} (hu : Odd u)
    (h : Int.ModEq (2 ^ K) (u * a) (u * b)) : Int.ModEq (2 ^ K) a b := by
  have hg : Int.gcd ((2 : ℤ) ^ K) u = 1 := by
    simpa [Int.gcd_def] using (hu.natAbs.coprime_two_right.symm.pow_left K).gcd_eq_one
  have hc := Int.ModEq.cancel_left_div_gcd (by positivity : 0 < (2 : ℤ) ^ K) h
  simpa [hg] using hc

theorem odd_periodic_modulus {L : ℕ} (hL : 0 < L) : Odd ((2 : ℤ) ^ L - 1) := by
  cases L with
  | zero => omega
  | succ L =>
      refine ⟨(2 : ℤ) ^ L - 1, ?_⟩
      rw [pow_succ]
      ring

/-- The repeated block is an index representative of its rational phase at
any requested binary precision. -/
theorem repeatedBlock_index_mod {L B : ℕ} {theta : ℚ}
    (hL : 0 < L)
    (hclock : ((2 : ℤ) ^ L - 1) * theta.num = -(theta.den : ℤ) * B) (K : ℕ) :
    Int.ModEq (2 ^ K) ((theta.den : ℤ) * (repeatedBlock L B K : ℤ)) theta.num := by
  have hp : Int.ModEq (2 ^ K) ((2 : ℤ) ^ (L * K)) 0 :=
    (pow_dvd_pow 2 (by nlinarith : K ≤ L * K)).modEq_zero_int
  have hq : Int.ModEq (2 ^ K)
      (((2 : ℤ) ^ L - 1) * (repeatedBlock L B K : ℤ)) (-(B : ℤ)) := by
    rw [repeatedBlock_geometric]
    convert (hp.sub (Int.ModEq.refl 1)).mul_left (B : ℤ) using 1; ring
  apply modEq_cancel_odd (odd_periodic_modulus hL)
  rw [hclock]
  convert hq.mul_left (theta.den : ℤ) using 1 <;> ring

/-- Equation (4) reduced modulo the requested precision. -/
theorem closed_repeatedBlock_modEq {c L B : ℕ} (hL : 0 < L) (hB : B < 2 ^ L)
    (K : ℕ) : Int.ModEq (2 ^ K)
      (((2 : ℤ) ^ L - 1) ^ 2 * (closed c (repeatedBlock L B K) : ℤ))
      (periodicNumerator c L B) := by
  have hp : Int.ModEq (2 ^ K) ((2 : ℤ) ^ (L * K)) 0 :=
    (pow_dvd_pow 2 (by nlinarith : K ≤ L * K)).modEq_zero_int
  rw [closed_repeatedBlock c L B K hB]
  simpa using (Int.ModEq.refl (periodicNumerator c L B)).add
    (hp.mul_right (((closed c B : ℤ) - 1) * ((2 : ℤ) ^ L - 1) +
      2 * c * L * B * (((K : ℤ) - 1) * (2 : ℤ) ^ L - K)))

/-- A represented periodic phase must have the exact rational value computed
by the finite repeated-block identity. -/
theorem periodicNumerator_eq_of_represents {c L B : ℕ} {theta : ℚ} {seed : ℤ}
    (hL : 0 < L) (hB : B < 2 ^ L)
    (hclock : ((2 : ℤ) ^ L - 1) * theta.num = -(theta.den : ℤ) * B)
    (h : represents c theta seed) :
    periodicNumerator c L B = ((2 : ℤ) ^ L - 1) ^ 2 * seed := by
  let delta := periodicNumerator c L B - ((2 : ℤ) ^ L - 1) ^ 2 * seed
  let K := delta.natAbs
  have hindex := repeatedBlock_index_mod hL hclock K
  have hseed := (h.2 K (repeatedBlock L B K) hindex).mul_left
    (((2 : ℤ) ^ L - 1) ^ 2)
  have hvalue := closed_repeatedBlock_modEq (c := c) hL hB K
  have hmod := hseed.symm.trans hvalue
  have hdvd : ((2 ^ K : ℕ) : ℤ) ∣ delta := hmod.dvd
  have hlt : delta.natAbs < Int.natAbs ((2 ^ K : ℕ) : ℤ) := by
    simp only [Int.natAbs_natCast]
    exact Nat.lt_two_pow_self
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt
  dsimp [delta] at hz
  omega

/-- Integrality of the periodic value imposes the finite divisibility
condition underlying the denominator restriction. -/
theorem periodic_modulus_dvd_of_integral {c L B : ℕ} {seed : ℤ}
    (hvalue : periodicNumerator c L B = ((2 : ℤ) ^ L - 1) ^ 2 * seed) :
    ((2 : ℤ) ^ L - 1) ∣ 2 * (c : ℤ) * L * B := by
  refine ⟨((2 : ℤ) ^ L - 1) * seed - ((2 : ℤ) ^ L - 1) +
    ((closed c B : ℤ) - 1) - 2 * (c : ℤ) * L * B, ?_⟩
  unfold periodicNumerator at hvalue
  linear_combination hvalue

/-- Every represented periodic rational phase has reduced denominator
dividing `2*c*L` (equation (6) of the note).  This is only a necessary condition. -/
theorem denominator_dvd_twice_coefficient_period {c L B : ℕ} {theta : ℚ} {seed : ℤ}
    (hL : 0 < L) (hB : B < 2 ^ L)
    (hclock : ((2 : ℤ) ^ L - 1) * theta.num = -(theta.den : ℤ) * B)
    (h : represents c theta seed) : theta.den ∣ 2 * c * L := by
  have hvalue := periodicNumerator_eq_of_represents hL hB hclock h
  obtain ⟨k, hk⟩ := periodic_modulus_dvd_of_integral hvalue
  have hM : (2 : ℤ) ^ L - 1 ≠ 0 := by
    obtain ⟨k, hk⟩ := odd_periodic_modulus hL
    omega
  have heq : ((2 : ℤ) ^ L - 1) * (2 * (c : ℤ) * L * theta.num) =
      ((2 : ℤ) ^ L - 1) * (-(theta.den : ℤ) * k) := by
    linear_combination (2 * (c : ℤ) * L) * hclock - (theta.den : ℤ) * hk
  have hcancel := mul_left_cancel₀ hM heq
  have hdvd : (theta.den : ℤ) ∣ (2 * (c : ℤ) * L) * theta.num := by
    refine ⟨-k, ?_⟩
    linear_combination hcancel
  have hcop : Int.gcd (theta.den : ℤ) theta.num = 1 := by
    simpa [Int.gcd_def, Nat.gcd_comm] using theta.reduced.gcd_eq_one
  have hdiv := Int.dvd_of_dvd_mul_left_of_gcd_one hdvd hcop
  exact_mod_cast hdiv

/-- An integral finite periodic value supplies an actual clock in the
finite-residue definition.  The numerator/denominator condition says exactly
that `theta = -B / (2^L - 1)`, without assuming that this fraction is reduced. -/
theorem represents_of_periodic {c L B : ℕ} {theta : ℚ} {seed : ℤ}
    (hL : 0 < L) (hB : B < 2 ^ L) (hodd : Odd theta.den)
    (hclock : ((2 : ℤ) ^ L - 1) * theta.num = -(theta.den : ℤ) * B)
    (hvalue : periodicNumerator c L B = ((2 : ℤ) ^ L - 1) ^ 2 * seed) :
    represents c theta seed := by
  refine ⟨hodd, ?_⟩
  intro K m hm
  let q := repeatedBlock L B K
  have hp : Int.ModEq (2 ^ K) ((2 : ℤ) ^ (L * K)) 0 := by
    apply Int.ModEq.symm
    apply Int.modEq_iff_dvd.mpr
    simp only [sub_zero]
    exact pow_dvd_pow 2 (by nlinarith : K ≤ L * K)
  have hM := odd_periodic_modulus hL
  have hq : Int.ModEq (2 ^ K) (((2 : ℤ) ^ L - 1) * (q : ℤ)) (-(B : ℤ)) := by
    change Int.ModEq (2 ^ K)
      (((2 : ℤ) ^ L - 1) * (repeatedBlock L B K : ℤ)) (-(B : ℤ))
    rw [repeatedBlock_geometric]
    convert (hp.sub (Int.ModEq.refl 1)).mul_left (B : ℤ) using 1; ring
  have hden : Odd (theta.den : ℤ) := by exact_mod_cast hodd
  have hmq : Int.ModEq (2 ^ K) (m : ℤ) (q : ℤ) := by
    apply modEq_cancel_odd hM
    apply modEq_cancel_odd hden
    have hm' := hm.mul_left ((2 : ℤ) ^ L - 1)
    have hq' := hq.mul_left (theta.den : ℤ)
    rw [hclock] at hm'
    simp only [neg_mul, mul_neg] at hm' hq'
    convert hm'.trans hq'.symm using 1; ring
  apply ((closed_modEq_iff c K m q).mpr hmq).trans
  apply modEq_cancel_odd (show Odd (((2 : ℤ) ^ L - 1) ^ 2) from hM.pow)
  have heval := closed_repeatedBlock c L B K hB
  rw [hvalue] at heval
  change Int.ModEq (2 ^ K)
    (((2 : ℤ) ^ L - 1) ^ 2 * (closed c (repeatedBlock L B K) : ℤ)) _
  rw [heval]
  simpa using (Int.ModEq.refl (((2 : ℤ) ^ L - 1) ^ 2 * seed)).add
    (hp.mul_right (((closed c B : ℤ) - 1) * ((2 : ℤ) ^ L - 1) +
      2 * c * L * B * (((K : ℤ) - 1) * (2 : ℤ) ^ L - K)))

/-- The four coefficient-twelve periodic phases, with no denominator search. -/
theorem represents_three_neg_one_third : represents 3 (-(1 : ℚ) / 3) 2 := by
  apply represents_of_periodic (L := 2) (B := 1)
  all_goals norm_num [periodicNumerator, closed, rulerSum, low, padicValNat]

theorem represents_three_neg_two_thirds : represents 3 (-(2 : ℚ) / 3) (-1) := by
  apply represents_of_periodic (L := 2) (B := 2)
  all_goals norm_num [periodicNumerator, closed, rulerSum, low, padicValNat]

theorem represents_three_neg_two_ninths : represents 3 (-(2 : ℚ) / 9) 3 := by
  have h14 : closed 3 14 = 387 := by
    have h1 := closed_two_mul_add_one 3 0
    have h3 := closed_two_mul_add_one 3 1
    have h7 := closed_two_mul_add_one 3 3
    have h14 := closed_two_mul_succ 3 7
    norm_num at h1 h3 h7 h14
    omega
  apply represents_of_periodic (L := 6) (B := 14)
  all_goals norm_num [periodicNumerator, h14]

theorem represents_three_neg_seven_ninths : represents 3 (-(7 : ℚ) / 9) (-2) := by
  have h49 : closed 3 49 = 1982 := by
    have h1 := closed_two_mul_add_one 3 0
    have h3 := closed_two_mul_add_one 3 1
    have h6 := closed_two_mul_succ 3 3
    have h12 := closed_two_mul_succ 3 6
    have h24 := closed_two_mul_succ 3 12
    have h49 := closed_two_mul_add_one 3 24
    norm_num at h1 h3 h6 h12 h24 h49
    omega
  apply represents_of_periodic (L := 6) (B := 49)
  all_goals norm_num [periodicNumerator, h49]

end RationalClockResearch

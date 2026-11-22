import RationalClockGeneral
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The rational clock on the 2-adic integers

The finite clock permutations lift to an actual self-map of `ℤ_[2]`.  This
module constructs the lift directly from its compatible residues, then builds
its inverse and metric structure.  The construction is deliberately tied to
`closedResidue`: its reduction modulo `2^K` is definitionally the finite clock
already used by the rational classification.
-/

namespace RationalClockResearch

private noncomputable def clockApprox (c : ℕ) (z : ℤ_[2]) (K : ℕ) : ℤ :=
  closed c (PadicInt.toZModPow K z).val

private theorem clockApprox_pow_dvd_sub (c : ℕ) (z : ℤ_[2]) (K : ℕ) :
    (2 : ℤ) ^ K ∣ clockApprox c z (K + 1) - clockApprox c z K := by
  let hi := PadicInt.toZModPow (K + 1) z
  let lo := PadicInt.toZModPow K z
  have hcast : ZMod.cast hi = lo := by
    change ZMod.cast (PadicInt.toZModPow (K + 1) z) = PadicInt.toZModPow K z
    exact PadicInt.cast_toZModPow K (K + 1) (Nat.le_succ K) z
  have hinput : Nat.ModEq (2 ^ K) lo.val hi.val := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [ZMod.natCast_zmod_val]
    simpa only [ZMod.cast_eq_val] using hcast.symm
  have hclosed := (closed_natModEq_iff c K lo.val hi.val).mpr hinput
  have hclosedInt : Int.ModEq (2 ^ K)
      (closed c lo.val : ℤ) (closed c hi.val : ℤ) := by
    exact_mod_cast hclosed
  simpa only [clockApprox, hi, lo, Nat.cast_pow, Nat.cast_ofNat] using hclosedInt.dvd

/-- The 2-adic clock obtained by lifting all finite closed-clock residues. -/
noncomputable def padicClock (c : ℕ) (z : ℤ_[2]) : ℤ_[2] :=
  PadicInt.ofIntSeq (clockApprox c z)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (clockApprox c z) 2 (clockApprox_pow_dvd_sub c z))

/-- The 2-adic clock reduces to the previously verified finite permutation at
every binary precision. -/
theorem padicClock_toZModPow (c K : ℕ) (z : ℤ_[2]) :
    PadicInt.toZModPow K (padicClock c z) =
      closedResidue c K (PadicInt.toZModPow K z) := by
  simpa only [padicClock, clockApprox, closedResidue, Int.cast_natCast] using
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
      (clockApprox c z) 2 (clockApprox_pow_dvd_sub c z) K

/-- Reduction of the finite clock commutes with lowering the precision. -/
theorem closedResidue_cast (c K L : ℕ) (hKL : K ≤ L) (z : ZMod (2 ^ L)) :
    ZMod.cast (closedResidue c L z) = closedResidue c K (ZMod.cast z) := by
  have hinput : Nat.ModEq (2 ^ K) ((ZMod.cast z : ZMod (2 ^ K))).val z.val := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [ZMod.natCast_zmod_val]
    exact ZMod.cast_eq_val z
  have hclosed :=
    (closed_natModEq_iff c K ((ZMod.cast z : ZMod (2 ^ K))).val z.val).mpr hinput
  change ZMod.cast (closed c z.val : ZMod (2 ^ L)) =
    (closed c (ZMod.cast z : ZMod (2 ^ K)).val : ZMod (2 ^ K))
  rw [ZMod.cast_natCast (pow_dvd_pow 2 hKL)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hclosed.symm

private noncomputable def inverseClockApprox (c : ℕ) (z : ℤ_[2]) (K : ℕ) : ℤ :=
  ((closedResidueEquiv c K).symm (PadicInt.toZModPow K z)).val

private theorem inverseClockApprox_pow_dvd_sub (c : ℕ) (z : ℤ_[2]) (K : ℕ) :
    (2 : ℤ) ^ K ∣ inverseClockApprox c z (K + 1) - inverseClockApprox c z K := by
  let hi := (closedResidueEquiv c (K + 1)).symm (PadicInt.toZModPow (K + 1) z)
  let lo := (closedResidueEquiv c K).symm (PadicInt.toZModPow K z)
  have hcast : ZMod.cast hi = lo := by
    apply closedResidue_injective c K
    calc
      closedResidue c K (ZMod.cast hi) =
          ZMod.cast (closedResidue c (K + 1) hi) :=
        (closedResidue_cast c K (K + 1) (Nat.le_succ K) hi).symm
      _ = ZMod.cast (PadicInt.toZModPow (K + 1) z) := by
        apply congrArg (fun w : ZMod (2 ^ (K + 1)) =>
          (ZMod.cast w : ZMod (2 ^ K)))
        exact (closedResidueEquiv c (K + 1)).apply_symm_apply _
      _ = PadicInt.toZModPow K z :=
        PadicInt.cast_toZModPow K (K + 1) (Nat.le_succ K) z
      _ = closedResidue c K lo :=
        ((closedResidueEquiv c K).apply_symm_apply _).symm
  have hinput : Nat.ModEq (2 ^ K) lo.val hi.val := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [ZMod.natCast_zmod_val]
    simpa only [ZMod.cast_eq_val] using hcast.symm
  have hinputInt : Int.ModEq (2 ^ K) (lo.val : ℤ) (hi.val : ℤ) := by
    exact_mod_cast hinput
  simpa only [inverseClockApprox, hi, lo, Nat.cast_pow, Nat.cast_ofNat] using hinputInt.dvd

/-- The inverse 2-adic clock, lifted from the inverses of all finite clock
permutations. -/
noncomputable def inversePadicClock (c : ℕ) (z : ℤ_[2]) : ℤ_[2] :=
  PadicInt.ofIntSeq (inverseClockApprox c z)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (inverseClockApprox c z) 2 (inverseClockApprox_pow_dvd_sub c z))

theorem inversePadicClock_toZModPow (c K : ℕ) (z : ℤ_[2]) :
    PadicInt.toZModPow K (inversePadicClock c z) =
      (closedResidueEquiv c K).symm (PadicInt.toZModPow K z) := by
  calc
    _ = (((closedResidueEquiv c K).symm
        (PadicInt.toZModPow K z)).val : ZMod (2 ^ K)) := by
      simpa only [inversePadicClock, inverseClockApprox, Int.cast_natCast] using
        PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
          (inverseClockApprox c z) 2 (inverseClockApprox_pow_dvd_sub c z) K
    _ = _ := ZMod.natCast_zmod_val _

theorem inversePadicClock_padicClock (c : ℕ) (z : ℤ_[2]) :
    inversePadicClock c (padicClock c z) = z := by
  apply PadicInt.ext_of_toZModPow.mp
  intro K
  rw [inversePadicClock_toZModPow, padicClock_toZModPow]
  exact (closedResidueEquiv c K).symm_apply_apply _

theorem padicClock_inversePadicClock (c : ℕ) (z : ℤ_[2]) :
    padicClock c (inversePadicClock c z) = z := by
  apply PadicInt.ext_of_toZModPow.mp
  intro K
  rw [padicClock_toZModPow, inversePadicClock_toZModPow]
  exact (closedResidueEquiv c K).apply_symm_apply _

/-- The finite binary isometries assemble into an equivalence of the 2-adic
integers. -/
noncomputable def padicClockEquiv (c : ℕ) : ℤ_[2] ≃ ℤ_[2] where
  toFun := padicClock c
  invFun := inversePadicClock c
  left_inv := inversePadicClock_padicClock c
  right_inv := padicClock_inversePadicClock c

theorem closedResidue_natCast (c K n : ℕ) :
    closedResidue c K (n : ZMod (2 ^ K)) = (closed c n : ZMod (2 ^ K)) := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  apply (closed_natModEq_iff c K _ _).mpr
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]

/-- On ordinary natural indices, the 2-adic clock is the original closed
formula. -/
@[simp] theorem padicClock_natCast (c n : ℕ) :
    padicClock c (n : ℤ_[2]) = (closed c n : ℤ_[2]) := by
  apply PadicInt.ext_of_toZModPow.mp
  intro K
  rw [padicClock_toZModPow]
  simp only [map_natCast]
  exact closedResidue_natCast c K n

@[simp] theorem padicClock_zero (c : ℕ) : padicClock c 0 = 1 := by
  simpa using padicClock_natCast c 0

/-- Equality modulo `2^K` is preserved and reflected by the lifted clock. -/
theorem padicClock_toZModPow_eq_iff (c K : ℕ) (x y : ℤ_[2]) :
    PadicInt.toZModPow K (padicClock c x) =
        PadicInt.toZModPow K (padicClock c y) ↔
      PadicInt.toZModPow K x = PadicInt.toZModPow K y := by
  rw [padicClock_toZModPow, padicClock_toZModPow]
  exact (closedResidue_injective c K).eq_iff

private theorem toZModPow_eq_iff_le_sub_valuation {x y : ℤ_[2]}
    (hxy : x ≠ y) (K : ℕ) :
    PadicInt.toZModPow K x = PadicInt.toZModPow K y ↔
      K ≤ (x - y).valuation := by
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker,
    PadicInt.ker_toZModPow,
    PadicInt.mem_span_pow_iff_le_valuation (x - y) hsub K]

/-- The lifted clock preserves the valuation of every difference. -/
theorem padicClock_sub_valuation (c : ℕ) {x y : ℤ_[2]} (hxy : x ≠ y) :
    (padicClock c x - padicClock c y).valuation = (x - y).valuation := by
  have hclock : padicClock c x ≠ padicClock c y :=
    (padicClockEquiv c).injective.ne hxy
  have hthreshold (K : ℕ) :
      K ≤ (padicClock c x - padicClock c y).valuation ↔
        K ≤ (x - y).valuation := by
    calc
      _ ↔ PadicInt.toZModPow K (padicClock c x) =
          PadicInt.toZModPow K (padicClock c y) :=
        (toZModPow_eq_iff_le_sub_valuation hclock K).symm
      _ ↔ PadicInt.toZModPow K x = PadicInt.toZModPow K y :=
        padicClock_toZModPow_eq_iff c K x y
      _ ↔ _ := toZModPow_eq_iff_le_sub_valuation hxy K
  apply Nat.le_antisymm
  · exact (hthreshold _).mp le_rfl
  · exact (hthreshold _).mpr le_rfl

/-- The actual 2-adic clock is an isometry. -/
theorem padicClock_isometry (c : ℕ) : Isometry (padicClock c) := by
  apply Isometry.of_dist_eq
  intro x y
  by_cases hxy : x = y
  · simp [hxy]
  · have hclock : padicClock c x ≠ padicClock c y :=
      (padicClockEquiv c).injective.ne hxy
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hclockSub : padicClock c x - padicClock c y ≠ 0 :=
      sub_ne_zero.mpr hclock
    rw [dist_eq_norm, dist_eq_norm,
      PadicInt.norm_eq_zpow_neg_valuation hclockSub,
      PadicInt.norm_eq_zpow_neg_valuation hsub,
      padicClock_sub_valuation c hxy]

/-- Isometric-equivalence packaging of the 2-adic rational clock. -/
noncomputable def padicClockIsometryEquiv (c : ℕ) : ℤ_[2] ≃ᵢ ℤ_[2] where
  toEquiv := padicClockEquiv c
  isometry_toFun := padicClock_isometry c

/-- The all-ones 2-adic index is sent to zero. -/
@[simp] theorem padicClock_neg_one (c : ℕ) :
    padicClock c (-1 : ℤ_[2]) = 0 := by
  apply PadicInt.ext_of_toZModPow.mp
  intro K
  rw [padicClock_toZModPow]
  let m := (PadicInt.toZModPow K (-1 : ℤ_[2])).val
  have hm : Int.ModEq (2 ^ K) (m : ℤ) (-1 : ℤ) := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simp only [Int.cast_natCast, Int.cast_neg, Int.cast_one]
    rw [ZMod.natCast_zmod_val]
    simp only [map_neg, map_one]
  have hclosed := (represents_neg_one c).2 K m (by simpa using hm)
  simp only [closedResidue, map_zero]
  change (closed c m : ZMod (2 ^ K)) = 0
  rw [← Int.cast_natCast, ← Int.cast_zero]
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr hclosed

@[simp] theorem inversePadicClock_zero (c : ℕ) :
    inversePadicClock c 0 = (-1 : ℤ_[2]) := by
  rw [← padicClock_neg_one c]
  exact inversePadicClock_padicClock c (-1)

/-- The 2-adic extension of the positive step, defined by transporting
translation by one through the clock equivalence. -/
noncomputable def padicStep (c : ℕ) (x : ℤ_[2]) : ℤ_[2] :=
  padicClock c (inversePadicClock c x + 1)

/-- The clock conjugates the 2-adic odometer to `padicStep`. -/
theorem padicClock_add_one (c : ℕ) (z : ℤ_[2]) :
    padicClock c (z + 1) = padicStep c (padicClock c z) := by
  rw [padicStep, inversePadicClock_padicClock]

/-- The continuous extension takes zero to one, matching the `low(0)=0`
convention rather than the totalized natural convention. -/
@[simp] theorem padicStep_zero (c : ℕ) : padicStep c 0 = 1 := by
  rw [padicStep, inversePadicClock_zero]
  norm_num

/-- On every positive natural input, the conjugated 2-adic step is exactly the
original natural-number step. -/
theorem padicStep_natCast {c x : ℕ} (hx : 0 < x) :
    padicStep c (x : ℤ_[2]) = (step c x : ℤ_[2]) := by
  let z := inversePadicClock c (x : ℤ_[2])
  have hz : padicClock c z = (x : ℤ_[2]) :=
    padicClock_inversePadicClock c (x : ℤ_[2])
  apply PadicInt.ext_of_toZModPow.mp
  intro K
  let m := (PadicInt.toZModPow K z).val
  have hres : closedResidue c K (PadicInt.toZModPow K z) =
      (x : ZMod (2 ^ K)) := by
    calc
      _ = PadicInt.toZModPow K (padicClock c z) :=
        (padicClock_toZModPow c K z).symm
      _ = PadicInt.toZModPow K (x : ℤ_[2]) := congrArg _ hz
      _ = _ := by simp
  have hmod : Nat.ModEq (2 ^ K) (closed c m) x := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [closedResidue, m, ZMod.natCast_zmod_val] using hres
  have hstepMod : Nat.ModEq (2 ^ K) (step c (closed c m)) (step c x) :=
    step_modEq_of_modEq c (closed_pos c m) hx hmod
  rw [padicStep, show inversePadicClock c (x : ℤ_[2]) = z by rfl,
    padicClock_toZModPow]
  simp only [map_natCast]
  have hinput : PadicInt.toZModPow K (z + 1) =
      (m + 1 : ZMod (2 ^ K)) := by
    simp only [map_add, map_one, m, ZMod.natCast_zmod_val]
  rw [hinput]
  calc
    closedResidue c K (m + 1 : ZMod (2 ^ K)) =
        (closed c (m + 1) : ZMod (2 ^ K)) := by
      convert closedResidue_natCast c K (m + 1) using 1
      simp only [Nat.cast_add, Nat.cast_one]
    _ = (step c (closed c m) : ZMod (2 ^ K)) := by
      rw [closed_succ_eq_step_of_low_eq c m (closed_low c m)]
    _ = (step c x : ZMod (2 ^ K)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hstepMod

/-- The transported step is itself an isometric equivalence. -/
noncomputable def padicStepIsometryEquiv (c : ℕ) : ℤ_[2] ≃ᵢ ℤ_[2] :=
  ((padicClockIsometryEquiv c).symm.trans
    (IsometryEquiv.vaddConst (1 : ℤ_[2]))).trans
      (padicClockIsometryEquiv c)

@[simp] theorem padicStepIsometryEquiv_apply (c : ℕ) (x : ℤ_[2]) :
    padicStepIsometryEquiv c x = padicStep c x := rfl

theorem padicStep_isometry (c : ℕ) : Isometry (padicStep c) :=
  (padicStepIsometryEquiv c).isometry

theorem padicStep_continuous (c : ℕ) : Continuous (padicStep c) :=
  (padicStepIsometryEquiv c).continuous

/-- Iterating the transported step is exactly addition by an ordinary natural
number on the clock side. -/
theorem padicStep_iterate_clock (c n : ℕ) (z : ℤ_[2]) :
    (padicStep c)^[n] (padicClock c z) = padicClock c (z + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, ← padicClock_add_one]
      push_cast
      abel_nf

/-- The new 2-adic dynamics restricts to every original positive natural
orbit. -/
theorem padicStep_iterate_natCast {c seed : ℕ} (hseed : 0 < seed) (n : ℕ) :
    (padicStep c)^[n] (seed : ℤ_[2]) = (orbit c seed n : ℤ_[2]) := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, orbit]
      exact padicStep_natCast (orbit_pos hseed)

/-- Translation by one, and hence the conjugated 2-adic dynamics, has no
nontrivial periodic points. -/
theorem padicStep_no_periodic_point (c : ℕ) {n : ℕ} (hn : 0 < n) (x : ℤ_[2]) :
    (padicStep c)^[n] x ≠ x := by
  intro hperiod
  let z := inversePadicClock c x
  have hx : x = padicClock c z := (padicClock_inversePadicClock c x).symm
  rw [hx, padicStep_iterate_clock] at hperiod
  have hadd : z + (n : ℤ_[2]) = z := (padicClockEquiv c).injective hperiod
  have hnzero : (n : ℤ_[2]) = 0 := by
    calc
      (n : ℤ_[2]) = (z + (n : ℤ_[2])) - z := by abel
      _ = 0 := by rw [hadd]; abel
  have : n = 0 := by exact_mod_cast hnzero
  omega

/-! ## Intrinsic low part and the explicit 2-adic recurrence -/

/-- The continuous 2-adic low part. Its value at zero is zero, unlike the
totalized natural helper `low`. -/
noncomputable def padicLow (x : ℤ_[2]) : ℤ_[2] :=
  by
    classical
    exact if hx : x = 0 then 0 else (2 : ℤ_[2]) ^ x.valuation

@[simp] theorem padicLow_zero : padicLow 0 = 0 := by
  simp [padicLow]

theorem padicInt_valuation_natCast (n : ℕ) :
    (n : ℤ_[2]).valuation = padicValNat 2 n := by
  simp only [PadicInt.valuation, PadicInt.coe_natCast, Padic.valuation_natCast,
    Int.toNat_natCast]

/-- On positive naturals, the intrinsic 2-adic low part is the original
power-of-two low part. -/
theorem padicLow_natCast {n : ℕ} (hn : 0 < n) :
    padicLow (n : ℤ_[2]) = (low n : ℤ_[2]) := by
  rw [padicLow, dif_neg (by exact_mod_cast (ne_of_gt hn)),
    padicInt_valuation_natCast n]
  simp only [low, Nat.cast_pow, Nat.cast_ofNat]

/-- The low part has exactly the norm of its input, including at zero. -/
theorem norm_padicLow (x : ℤ_[2]) : ‖padicLow x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [padicLow, dif_neg hx]
    change ‖((2 : ℕ) : ℤ_[2]) ^ x.valuation‖ = ‖x‖
    rw [PadicInt.norm_p_pow (p := 2) x.valuation,
      PadicInt.norm_eq_zpow_neg_valuation hx]

private theorem padicInt_valuation_eq_of_norm_eq {x y : ℤ_[2]}
    (hx : x ≠ 0) (hy : y ≠ 0) (h : ‖x‖ = ‖y‖) :
    x.valuation = y.valuation := by
  have hpow := h
  rw [PadicInt.norm_eq_zpow_neg_valuation hx,
    PadicInt.norm_eq_zpow_neg_valuation hy] at hpow
  have hexp : -(x.valuation : ℤ) = -(y.valuation : ℤ) :=
    zpow_right_injective₀ (a := (2 : ℝ)) (by norm_num) (by norm_num) hpow
  exact_mod_cast (neg_inj.mp hexp)

/-- The intrinsic low-part map is continuous on all of `ℤ_[2]`; continuity at
zero is exactly why its zero value is defined to be zero. -/
theorem padicLow_continuous : Continuous padicLow := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  by_cases hx : x = 0
  · subst x
    refine ⟨ε, hε, ?_⟩
    intro y hy
    simpa only [padicLow_zero, dist_zero_right, norm_padicLow,
      dist_zero_right] using hy
  · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    refine ⟨‖x‖, hxnorm, ?_⟩
    intro y hy
    have hdiff : ‖y - x‖ < ‖x‖ := by
      simpa only [dist_eq_norm] using hy
    have hyne : y ≠ 0 := by
      intro hyzero
      subst y
      simp only [zero_sub, norm_neg, lt_self_iff_false] at hdiff
    have hnorm : ‖y‖ = ‖x‖ := by
      have hne : ‖y - x‖ ≠ ‖x‖ := ne_of_lt hdiff
      have hadd := PadicInt.norm_add_eq_max_of_ne hne
      simpa only [sub_add_cancel, max_eq_right hdiff.le] using hadd
    have hval : y.valuation = x.valuation :=
      padicInt_valuation_eq_of_norm_eq hyne hx hnorm
    have hlow : padicLow y = padicLow x := by
      simp [padicLow, hyne, hx, hval]
    rw [hlow, dist_self]
    exact hε

/-- The valuation formula gives the transported dynamics explicitly. This is
the genuine 2-adic extension of `x ↦ x + 4*c*low(x) + 1`. -/
theorem padicStep_eq_explicit (c : ℕ) (x : ℤ_[2]) :
    padicStep c x = x + ((4 * c : ℕ) : ℤ_[2]) * padicLow x + 1 := by
  let explicitStep : ℤ_[2] → ℤ_[2] :=
    fun y => y + ((4 * c : ℕ) : ℤ_[2]) * padicLow y + 1
  have hexplicit : Continuous explicitStep := by
    dsimp only [explicitStep]
    exact (continuous_id.add (continuous_const.mul padicLow_continuous)).add
      continuous_const
  have honNat (n : ℕ) :
      padicStep c (n : ℤ_[2]) = explicitStep (n : ℤ_[2]) := by
    by_cases hn : n = 0
    · subst n
      simp [explicitStep]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [padicStep_natCast hnpos]
      dsimp only [explicitStep]
      rw [padicLow_natCast hnpos]
      norm_cast
  have heq : padicStep c = explicitStep :=
    PadicInt.denseRange_natCast.equalizer (padicStep_continuous c) hexplicit
      (funext honNat)
  exact congrFun heq x

/-- The clock transfers the valuation of `z+1` to the clock value. Mathlib's
total valuation convention makes the identity valid at `z=-1` as well. -/
theorem padicClock_valuation (c : ℕ) (z : ℤ_[2]) :
    (padicClock c z).valuation = (z + 1).valuation := by
  by_cases hz : z = -1
  · subst z
    simp
  · have h := padicClock_sub_valuation c hz
        (y := (-1 : ℤ_[2]))
    simpa only [padicClock_neg_one, sub_zero, sub_neg_eq_add] using h

/-- Headline conjugacy in explicit form: the rational clock sends the adding
machine on `ℤ_[2]` to the continuous low-part recurrence. -/
theorem padicClock_explicit_conjugacy (c : ℕ) (z : ℤ_[2]) :
    padicClock c (z + 1) =
      padicClock c z + ((4 * c : ℕ) : ℤ_[2]) *
        padicLow (padicClock c z) + 1 := by
  rw [padicClock_add_one, padicStep_eq_explicit]

/-- Nonnegative ordinary integers remain dense after translation by any
2-adic integer. -/
theorem denseRange_add_natCast (z : ℤ_[2]) :
    DenseRange (fun n : ℕ => z + (n : ℤ_[2])) := by
  have htranslate : DenseRange (fun y : ℤ_[2] => y + z) :=
    (IsometryEquiv.vaddConst z).surjective.denseRange
  have hcomp := htranslate.comp PadicInt.denseRange_natCast
    (IsometryEquiv.vaddConst z).continuous
  convert hcomp using 1
  funext n
  simp only [Function.comp_apply, add_comm]

/-- Every orbit of the 2-adic recurrence is dense. Equivalently, the
conjugated system is minimal, just like the adding machine. -/
theorem padicStep_orbit_dense (c : ℕ) (x : ℤ_[2]) :
    DenseRange (fun n : ℕ => (padicStep c)^[n] x) := by
  let z := inversePadicClock c x
  have hx : x = padicClock c z := (padicClock_inversePadicClock c x).symm
  have hclockRange : DenseRange
      (padicClock c ∘ fun n : ℕ => z + (n : ℤ_[2])) :=
    (padicClockEquiv c).surjective.denseRange.comp
      (denseRange_add_natCast z) (padicClockIsometryEquiv c).continuous
  rw [hx]
  convert hclockRange using 1
  funext n
  exact padicStep_iterate_clock c n z

end RationalClockResearch

import RationalClockClassification

/-!
# A uniform finite classification of rational-clock tails

The integral phase bound leaves `2 * c - 2` possible signed seeds for a
nonintegral phase reduced to `(-1, 0)`: the integers from `1 - c` through `c`,
apart from the endpoint seeds `0` and `1`. A positive signed seed is already
an ordinary seed. One forward clock tick sends every negative candidate to a
positive seed. Together with the integer-clock class represented by `1`, this
gives at most `2 * c - 1` common-future classes.

The finite set below is filtered by actual representability. Thus every one
of its members is a genuine rational-clock seed; no existence claim is made
for phase slots that the integral bound permits but the dynamics omit.
-/

namespace RationalClockResearch

/-- The signed seed slots allowed by the integral phase bound. -/
noncomputable def phaseSeedCandidates (c : ℕ) : Finset ℤ :=
  (((Finset.Icc ((1 : ℤ) - c) (c : ℤ)).erase 0).erase 1)

/-- A signed slot is admissible when some reduced nonintegral rational phase
actually represents it. -/
def admissiblePhaseSeed (c : ℕ) (s : ℤ) : Prop :=
  ∃ theta : ℚ, -1 < theta ∧ theta < 0 ∧ represents c theta s

/-- Turn a nonzero signed phase seed into a positive ordinary seed. Positive
seeds are unchanged; negative seeds are advanced by one clock tick. -/
def positiveRepresentative (c : ℕ) (s : ℤ) : ℕ :=
  if 0 < s then s.toNat
  else (s + 4 * (c : ℤ) * (low s.natAbs : ℤ) + 1).toNat

/-- The actual positive representatives used by the general classification. -/
noncomputable def generalClassRepresentatives (c : ℕ) : Finset ℕ :=
  by
    classical
    exact insert 1
      (((phaseSeedCandidates c).filter (admissiblePhaseSeed c)).image
        (positiveRepresentative c))

theorem phaseSeedCandidates_card {c : ℕ} (hc : 0 < c) :
    (phaseSeedCandidates c).card = 2 * c - 2 := by
  have hzero : (0 : ℤ) ∈ Finset.Icc ((1 : ℤ) - c) (c : ℤ) := by
    simp only [Finset.mem_Icc]
    constructor <;> omega
  have hone : (1 : ℤ) ∈ (Finset.Icc ((1 : ℤ) - c) (c : ℤ)).erase 0 := by
    simp only [Finset.mem_erase, Finset.mem_Icc]
    constructor
    · norm_num
    · constructor <;> omega
  rw [phaseSeedCandidates, Finset.card_erase_of_mem hone,
    Finset.card_erase_of_mem hzero, Int.card_Icc]
  omega

theorem positiveRepresentative_pos {c : ℕ} (hc : 0 < c) {s : ℤ}
    (hlower : (1 : ℤ) - c ≤ s) (hszero : s ≠ 0) :
    0 < positiveRepresentative c s := by
  by_cases hspos : 0 < s
  · simp only [positiveRepresentative, if_pos hspos]
    have hcast : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hspos.le
    apply Int.natCast_pos.mp
    rw [hcast]
    exact hspos
  · have hsneg : s < 0 := by omega
    have hlow : (0 : ℤ) < (low s.natAbs : ℕ) := by
      exact_mod_cast low_pos s.natAbs
    have hvalue : (0 : ℤ) < s + 4 * (c : ℤ) * (low s.natAbs : ℤ) + 1 := by
      have hcZ : (0 : ℤ) < c := by exact_mod_cast hc
      nlinarith
    simp only [positiveRepresentative, if_neg hspos]
    apply Int.natCast_pos.mp
    rw [Int.toNat_of_nonneg hvalue.le]
    exact hvalue

/-- Every admissible signed slot supplies the advertised positive rational
clock representative. -/
theorem positiveRepresentative_has_clock {c : ℕ} (hc : 0 < c) {s : ℤ}
    (hlower : (1 : ℤ) - c ≤ s) (hszero : s ≠ 0)
    (hs : admissiblePhaseSeed c s) :
    hasRationalClock c (positiveRepresentative c s) := by
  obtain ⟨theta, _hlo, _hhi, htheta⟩ := hs
  by_cases hspos : 0 < s
  · refine ⟨theta, ?_⟩
    have hcast : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hspos.le
    simpa only [positiveRepresentative, if_pos hspos, hcast] using htheta
  · have hvalue : (0 : ℤ) < s + 4 * (c : ℤ) * (low s.natAbs : ℤ) + 1 := by
      have hsneg : s < 0 := by omega
      have hlow : (0 : ℤ) < (low s.natAbs : ℕ) := by
        exact_mod_cast low_pos s.natAbs
      have hcZ : (0 : ℤ) < c := by exact_mod_cast hc
      nlinarith
    refine ⟨theta + 1, ?_⟩
    have hnext := represents_add_one htheta hszero
    have hcast : (((s + 4 * (c : ℤ) * (low s.natAbs : ℤ) + 1).toNat : ℕ) : ℤ) =
        s + 4 * (c : ℤ) * (low s.natAbs : ℤ) + 1 :=
      Int.toNat_of_nonneg hvalue.le
    simpa only [positiveRepresentative, if_neg hspos, hcast] using hnext

theorem sameFuture_positiveRepresentative {c seed : ℕ} (hc : 0 < c)
    (hseed : 0 < seed) {theta phi : ℚ} {s : ℤ}
    (htheta : represents c theta (seed : ℤ)) (hphi : represents c phi s)
    (hlower : (1 : ℤ) - c ≤ s) (hszero : s ≠ 0)
    (j : ℤ) (hj : theta + j = phi) :
    sameFuture c seed (positiveRepresentative c s) := by
  have hrepPos := positiveRepresentative_pos hc hlower hszero
  by_cases hspos : 0 < s
  · have hcast : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hspos.le
    have hrep : represents c phi (positiveRepresentative c s : ℤ) := by
      simpa only [positiveRepresentative, if_pos hspos, hcast] using hphi
    exact sameFuture_of_shifted_clock htheta hrep hseed hrepPos j hj
  · have hvalue : (0 : ℤ) < s + 4 * (c : ℤ) * (low s.natAbs : ℤ) + 1 := by
      have hsneg : s < 0 := by omega
      have hlow : (0 : ℤ) < (low s.natAbs : ℕ) := by
        exact_mod_cast low_pos s.natAbs
      have hcZ : (0 : ℤ) < c := by exact_mod_cast hc
      nlinarith
    have hnext := represents_add_one hphi hszero
    have hcast : (((s + 4 * (c : ℤ) * (low s.natAbs : ℤ) + 1).toNat : ℕ) : ℤ) =
        s + 4 * (c : ℤ) * (low s.natAbs : ℤ) + 1 :=
      Int.toNat_of_nonneg hvalue.le
    have hrep : represents c (phi + 1) (positiveRepresentative c s : ℤ) := by
      simpa only [positiveRepresentative, if_neg hspos, hcast] using hnext
    apply sameFuture_of_shifted_clock htheta hrep hseed hrepPos (j + 1)
    push_cast
    linarith

/-- Uniform `2c-1` theorem. The displayed finite set has at most `2c-1`
members, every member is a positive rational-clock seed, and it classifies all
positive rational-clock seeds up to common future. -/
theorem generalClassClassification {c : ℕ} (hc : 0 < c) :
    (generalClassRepresentatives c).card ≤ 2 * c - 1 ∧
    (∀ r ∈ generalClassRepresentatives c,
      0 < r ∧ hasRationalClock c r) ∧
    (∀ seed : ℕ, 0 < seed →
      (hasRationalClock c seed ↔
        ∃ r ∈ generalClassRepresentatives c, sameFuture c seed r)) := by
  classical
  have hcandidateCard :
      ((phaseSeedCandidates c).filter (admissiblePhaseSeed c)).card ≤ 2 * c - 2 := by
    calc
      _ ≤ (phaseSeedCandidates c).card := Finset.card_filter_le _ _
      _ = 2 * c - 2 := phaseSeedCandidates_card hc
  have himageCard :
      (((phaseSeedCandidates c).filter (admissiblePhaseSeed c)).image
        (positiveRepresentative c)).card ≤ 2 * c - 2 :=
    (Finset.card_image_le).trans hcandidateCard
  have hrepresentatives : ∀ r ∈ generalClassRepresentatives c,
      0 < r ∧ hasRationalClock c r := by
    intro r hr
    simp only [generalClassRepresentatives, Finset.mem_insert, Finset.mem_image,
      Finset.mem_filter] at hr
    rcases hr with rfl | ⟨s, ⟨hslot, hadmissible⟩, rfl⟩
    · exact ⟨by decide, hasRationalClock_closed c 0⟩
    · have hb := hslot
      simp only [phaseSeedCandidates, Finset.mem_erase, Finset.mem_Icc] at hb
      exact ⟨positiveRepresentative_pos hc hb.2.2.1 hb.2.1,
        positiveRepresentative_has_clock hc hb.2.2.1 hb.2.1 hadmissible⟩
  refine ⟨?_, hrepresentatives, ?_⟩
  · calc
      (generalClassRepresentatives c).card ≤
          (((phaseSeedCandidates c).filter (admissiblePhaseSeed c)).image
            (positiveRepresentative c)).card + 1 := by
              simpa only [generalClassRepresentatives] using
                (Finset.card_insert_le 1
                  (((phaseSeedCandidates c).filter (admissiblePhaseSeed c)).image
                    (positiveRepresentative c)))
      _ ≤ (2 * c - 2) + 1 := Nat.add_le_add_right himageCard 1
      _ = 2 * c - 1 := by omega
  · intro seed hseed
    constructor
    · rintro ⟨theta, htheta⟩
      by_cases hint : ∃ z : ℤ, theta = (z : ℚ)
      · obtain ⟨z, rfl⟩ := hint
        obtain ⟨m, hm⟩ := closed_of_integer_clock hseed htheta
        refine ⟨1, Finset.mem_insert_self 1 _, ?_⟩
        exact ⟨0, m, by simpa [orbit, orbit_one_eq_closed] using hm⟩
      · have hnon : ∀ z : ℤ, theta ≠ (z : ℚ) := by simpa using hint
        obtain ⟨j, s, hlo, hhi, hs⟩ := exists_reduced_phase htheta hnon
        have hb := integralPhaseBound c (theta + j) s hc hlo hhi hs
        have hslot : s ∈ phaseSeedCandidates c := by
          simp only [phaseSeedCandidates, Finset.mem_erase, Finset.mem_Icc]
          exact ⟨hb.2.2.2, ⟨hb.2.2.1, ⟨hb.1, hb.2.1⟩⟩⟩
        have hadmissible : admissiblePhaseSeed c s :=
          ⟨theta + j, hlo, hhi, hs⟩
        refine ⟨positiveRepresentative c s, ?_, ?_⟩
        · simp only [generalClassRepresentatives, Finset.mem_insert,
            Finset.mem_image, Finset.mem_filter]
          exact Or.inr ⟨s, ⟨hslot, hadmissible⟩, rfl⟩
        · exact sameFuture_positiveRepresentative hc hseed htheta hs hb.1 hb.2.2.1 j rfl
    · rintro ⟨r, hr, hfuture⟩
      have hrinfo := hrepresentatives r hr
      exact hasRationalClock_of_sameFuture hseed hrinfo.1 hfuture hrinfo.2

end RationalClockResearch

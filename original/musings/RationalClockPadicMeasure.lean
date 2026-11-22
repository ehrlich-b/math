import RationalClockPadic
import Mathlib.Dynamics.Ergodic.Action.OfMinimal
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Quantitative dynamics of the 2-adic rational clock

The topological conjugacy from `RationalClockPadic` is quantitatively rigid.
Every block of `2^K` successive iterates visits every residue modulo `2^K`
exactly once.  We use these finite equidistribution statements to identify the
normalized additive Haar measure, prove that the clock and its transported step
preserve it, and prove uniqueness among invariant probability measures.
-/

namespace RationalClockResearch

open Filter Function MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal NNReal

noncomputable instance padicIntMeasurableSpace : MeasurableSpace ℤ_[2] :=
  borel ℤ_[2]

instance padicIntBorelSpace : BorelSpace ℤ_[2] := ⟨rfl⟩

/-! ## Exact finite-level equidistribution -/

private def finZModEquiv (K : ℕ) : Fin (2 ^ K) ≃ ZMod (2 ^ K) where
  toFun n := (n.1 : ZMod (2 ^ K))
  invFun a := ⟨a.val, a.val_lt⟩
  left_inv n := Fin.ext (ZMod.val_natCast_of_lt n.2)
  right_inv a := ZMod.natCast_zmod_val a

private theorem closedResidueEquiv_apply (c K : ℕ) (a : ZMod (2 ^ K)) :
    closedResidueEquiv c K a = closedResidue c K a := rfl

/-- At precision `K`, a block of `2^K` successive clock iterates is an
equivalence from the time slots to all binary residues. -/
noncomputable def padicOrbitResidueEquiv (c K : ℕ) (x : ℤ_[2]) :
    Fin (2 ^ K) ≃ ZMod (2 ^ K) :=
  finZModEquiv K |>.trans
    (Equiv.addLeft (PadicInt.toZModPow K (inversePadicClock c x))) |>.trans
      (closedResidueEquiv c K)

theorem padicOrbitResidueEquiv_apply (c K : ℕ) (x : ℤ_[2])
    (n : Fin (2 ^ K)) :
    padicOrbitResidueEquiv c K x n =
      PadicInt.toZModPow K ((padicStep c)^[n.1] x) := by
  let z := inversePadicClock c x
  have hx : x = padicClock c z := (padicClock_inversePadicClock c x).symm
  rw [hx, padicStep_iterate_clock, padicClock_toZModPow]
  simp [padicOrbitResidueEquiv, finZModEquiv, z,
    inversePadicClock_padicClock, map_add, closedResidueEquiv_apply]

/-- Every residue occurs at a unique time in each block of length `2^K`. -/
theorem padicStep_residue_existsUnique (c K : ℕ) (x : ℤ_[2])
    (a : ZMod (2 ^ K)) :
    ∃! n : Fin (2 ^ K),
      PadicInt.toZModPow K ((padicStep c)^[n.1] x) = a := by
  let e := padicOrbitResidueEquiv c K x
  refine ⟨e.symm a, ?_, ?_⟩
  · change PadicInt.toZModPow K ((padicStep c)^[(e.symm a).1] x) = a
    rw [← padicOrbitResidueEquiv_apply]
    exact e.apply_symm_apply a
  · intro n hn
    apply e.injective
    rw [padicOrbitResidueEquiv_apply, hn]
    exact (e.apply_symm_apply a).symm

/-- Counting form of exact finite-level equidistribution. -/
theorem padicStep_residue_count (c K : ℕ) (x : ℤ_[2])
    (a : ZMod (2 ^ K)) :
    (Finset.univ.filter fun n : Fin (2 ^ K) =>
      PadicInt.toZModPow K ((padicStep c)^[n.1] x) = a).card = 1 := by
  rw [Finset.card_eq_one_iff_existsUnique]
  simpa using padicStep_residue_existsUnique c K x a

/-- Every observable depending only on the residue modulo `2^K` has its exact
space average on every full orbit block of length `2^K`. -/
theorem padicStep_residue_sum {M : Type*} [AddCommMonoid M]
    (c K : ℕ) (x : ℤ_[2]) (f : ZMod (2 ^ K) → M) :
    (∑ n : Fin (2 ^ K),
      f (PadicInt.toZModPow K ((padicStep c)^[n.1] x))) =
        ∑ a : ZMod (2 ^ K), f a := by
  simpa only [← padicOrbitResidueEquiv_apply] using
    (padicOrbitResidueEquiv c K x).sum_comp f

/-! ## Binary cylinders and normalized Haar measure -/

/-- The clopen cylinder consisting of 2-adic integers with prescribed residue
at precision `K`. -/
def padicCylinder (K : ℕ) (a : ZMod (2 ^ K)) : Set ℤ_[2] :=
  {x | PadicInt.toZModPow K x = a}

theorem mem_padicCylinder_iff (K : ℕ) (a : ZMod (2 ^ K)) (x : ℤ_[2]) :
    x ∈ padicCylinder K a ↔ PadicInt.toZModPow K x = a := Iff.rfl

theorem toZModPow_eq_iff_dist_le (K : ℕ) (x y : ℤ_[2]) :
    PadicInt.toZModPow K x = PadicInt.toZModPow K y ↔
      dist x y ≤ ((2 : ℕ) : ℝ) ^ (-(K : ℤ)) := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker,
    PadicInt.ker_toZModPow]
  simpa only [dist_eq_norm] using
    (PadicInt.norm_le_pow_iff_mem_span_pow (x - y) K).symm

theorem padicCylinder_eq_closedBall (K : ℕ) (a : ZMod (2 ^ K)) :
    padicCylinder K a =
      closedBall (a.val : ℤ_[2]) (((2 : ℕ) : ℝ) ^ (-(K : ℤ))) := by
  ext x
  rw [mem_padicCylinder_iff, Metric.mem_closedBall,
    ← toZModPow_eq_iff_dist_le]
  simp only [map_natCast, ZMod.natCast_zmod_val]

theorem isClopen_padicCylinder (K : ℕ) (a : ZMod (2 ^ K)) :
    IsClopen (padicCylinder K a) := by
  rw [padicCylinder_eq_closedBall]
  exact ⟨isClosed_closedBall,
    IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (by norm_num))⟩

theorem measurableSet_padicCylinder (K : ℕ) (a : ZMod (2 ^ K)) :
    MeasurableSet (padicCylinder K a) :=
  (isClopen_padicCylinder K a).2.measurableSet

/-- All binary residue cylinders form a topological basis of `ℤ_[2]`. -/
theorem isTopologicalBasis_padicCylinder :
    TopologicalSpace.IsTopologicalBasis
      {s : Set ℤ_[2] | ∃ K : ℕ, ∃ a : ZMod (2 ^ K), s = padicCylinder K a} := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨K, a, rfl⟩
    exact (isClopen_padicCylinder K a).2
  · intro x U hxU hU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
    obtain ⟨K, hK⟩ := PadicInt.exists_pow_neg_lt 2 hε
    refine ⟨padicCylinder K (PadicInt.toZModPow K x),
      ⟨K, PadicInt.toZModPow K x, rfl⟩, ?_, ?_⟩
    · rfl
    · rw [show padicCylinder K (PadicInt.toZModPow K x) =
          closedBall x (((2 : ℕ) : ℝ) ^ (-(K : ℤ))) by
          ext y
          exact toZModPow_eq_iff_dist_le K y x]
      exact (closedBall_subset_ball hK).trans hball

theorem isPiSystem_padicCylinder :
    IsPiSystem
      {s : Set ℤ_[2] | ∃ K : ℕ, ∃ a : ZMod (2 ^ K), s = padicCylinder K a} := by
  rintro s ⟨K, a, rfl⟩ t ⟨L, b, rfl⟩ hnonempty
  rw [padicCylinder_eq_closedBall, padicCylinder_eq_closedBall] at hnonempty ⊢
  rcases IsUltrametricDist.closedBall_subset_trichotomy
      (a.val : ℤ_[2]) (b.val : ℤ_[2])
      (((2 : ℕ) : ℝ) ^ (-(K : ℤ)))
      (((2 : ℕ) : ℝ) ^ (-(L : ℤ))) with h | h | h
  · refine ⟨K, a, ?_⟩
    rw [padicCylinder_eq_closedBall]
    exact inter_eq_left.mpr h
  · refine ⟨L, b, ?_⟩
    rw [padicCylinder_eq_closedBall]
    exact inter_eq_right.mpr h
  · obtain ⟨z, hza, hzb⟩ := hnonempty
    exact ((Set.disjoint_left.mp h) hza hzb).elim

private noncomputable def padicUnitPositiveCompact :
    TopologicalSpace.PositiveCompacts ℤ_[2] :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Additive Haar probability measure on the compact group `ℤ_[2]`, normalized
to give the whole space mass one. -/
noncomputable def padicHaar : Measure ℤ_[2] :=
  Measure.addHaarMeasure padicUnitPositiveCompact

noncomputable instance padicHaarIsAddHaarMeasure :
    Measure.IsAddHaarMeasure padicHaar := by
  dsimp only [padicHaar]
  infer_instance

noncomputable instance : IsProbabilityMeasure padicHaar :=
  IsProbabilityMeasure.mk (by
    simpa [padicHaar, padicUnitPositiveCompact] using
      (Measure.addHaarMeasure_self (K₀ := padicUnitPositiveCompact)))

theorem padicHaar_cylinder_eq (K : ℕ) (a b : ZMod (2 ^ K)) :
    padicHaar (padicCylinder K a) = padicHaar (padicCylinder K b) := by
  let d : ℤ_[2] := (b.val : ℤ_[2]) - (a.val : ℤ_[2])
  have hpre : (fun z : ℤ_[2] => d + z) ⁻¹' padicCylinder K b =
      padicCylinder K a := by
    ext z
    simp only [Set.mem_preimage, mem_padicCylinder_iff, map_add, d, map_sub,
      map_natCast, ZMod.natCast_zmod_val]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  rw [← measure_preimage_add padicHaar d (padicCylinder K b), hpre]

/-- Every precision-`K` cylinder has Haar mass exactly `2⁻ᴷ`. -/
theorem padicHaar_padicCylinder (K : ℕ) (a : ZMod (2 ^ K)) :
    padicHaar (padicCylinder K a) = ((2 ^ K : ℕ) : ℝ≥0∞)⁻¹ := by
  have hsum := MeasureTheory.sum_measure_preimage_singleton
    (μ := padicHaar) (Finset.univ : Finset (ZMod (2 ^ K)))
    (f := PadicInt.toZModPow K) (fun b _ => measurableSet_padicCylinder K b)
  have hsum' : (∑ b : ZMod (2 ^ K), padicHaar (padicCylinder K b)) = 1 := by
    calc
      _ = ∑ b : ZMod (2 ^ K),
          padicHaar (PadicInt.toZModPow K ⁻¹' ({b} : Set (ZMod (2 ^ K)))) := by
        apply Finset.sum_congr rfl
        intro b _
        congr 1
      _ = padicHaar (PadicInt.toZModPow K ⁻¹'
          (↑(Finset.univ : Finset (ZMod (2 ^ K))) : Set (ZMod (2 ^ K)))) := hsum
      _ = 1 := by simp
  have hmul : padicHaar (padicCylinder K a) * ((2 ^ K : ℕ) : ℝ≥0∞) = 1 := by
    calc
      _ = ((2 ^ K : ℕ) : ℝ≥0∞) * padicHaar (padicCylinder K a) := mul_comm _ _
      _ = ∑ _b : ZMod (2 ^ K), padicHaar (padicCylinder K a) := by
        simp [ZMod.card]
      _ = ∑ b : ZMod (2 ^ K), padicHaar (padicCylinder K b) := by
        apply Finset.sum_congr rfl
        intro b _
        exact padicHaar_cylinder_eq K a b
      _ = 1 := hsum'
  exact ENNReal.eq_inv_of_mul_eq_one_left hmul

/-! ## Haar preservation and unique ergodicity -/

theorem padicClock_preserves_haar (c : ℕ) :
    MeasurePreserving (padicClock c) padicHaar padicHaar := by
  refine ⟨(padicClock_isometry c).continuous.measurable, ?_⟩
  apply MeasureTheory.ext_of_generate_finite
    {s : Set ℤ_[2] | ∃ K : ℕ, ∃ a : ZMod (2 ^ K), s = padicCylinder K a}
  · exact BorelSpace.measurable_eq.trans
      isTopologicalBasis_padicCylinder.borel_eq_generateFrom
  · exact isPiSystem_padicCylinder
  · rintro _ ⟨K, a, rfl⟩
    rw [Measure.map_apply (padicClock_isometry c).continuous.measurable
      (measurableSet_padicCylinder K a)]
    have hpre : padicClock c ⁻¹' padicCylinder K a =
        padicCylinder K ((closedResidueEquiv c K).symm a) := by
      ext z
      simp only [Set.mem_preimage, mem_padicCylinder_iff, padicClock_toZModPow]
      exact (Equiv.eq_symm_apply (closedResidueEquiv c K)).symm
    rw [hpre, padicHaar_cylinder_eq K]
  · rw [Measure.map_apply (padicClock_isometry c).continuous.measurable
      MeasurableSet.univ]
    simp

theorem padicStep_preserves_haar (c : ℕ) :
    MeasurePreserving (padicStep c) padicHaar padicHaar := by
  let e : ℤ_[2] ≃ᵐ ℤ_[2] :=
    (padicClockIsometryEquiv c).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e padicHaar padicHaar :=
    padicClock_preserves_haar c
  have hadd : MeasurePreserving (fun z : ℤ_[2] => z + 1) padicHaar padicHaar := by
    simpa only [add_comm] using measurePreserving_add_left padicHaar (1 : ℤ_[2])
  have hconj := he.comp (hadd.comp (MeasurePreserving.symm e he))
  change MeasurePreserving
    (fun x => padicClock c (inversePadicClock c x + 1)) padicHaar padicHaar at hconj
  exact hconj

private theorem add_one_iterate (n : ℕ) (z : ℤ_[2]) :
    (fun y : ℤ_[2] => y + 1)^[n] z = z + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      push_cast
      abel

private theorem add_one_invariant_cylinder_eq {ν : Measure ℤ_[2]}
    (hν : MeasurePreserving (fun z : ℤ_[2] => z + 1) ν ν)
    (K : ℕ) (a b : ZMod (2 ^ K)) :
    ν (padicCylinder K a) = ν (padicCylinder K b) := by
  let n := (b - a).val
  have hpre : ((fun z : ℤ_[2] => z + 1)^[n]) ⁻¹' padicCylinder K b =
      padicCylinder K a := by
    ext z
    simp only [Set.mem_preimage, mem_padicCylinder_iff, add_one_iterate,
      map_add, map_natCast, n, ZMod.natCast_zmod_val]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  rw [← hpre]
  exact (hν.iterate n).measure_preimage
    (measurableSet_padicCylinder K b).nullMeasurableSet

private theorem add_one_invariant_cylinder {ν : Measure ℤ_[2]}
    [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun z : ℤ_[2] => z + 1) ν ν)
    (K : ℕ) (a : ZMod (2 ^ K)) :
    ν (padicCylinder K a) = ((2 ^ K : ℕ) : ℝ≥0∞)⁻¹ := by
  have hsum := MeasureTheory.sum_measure_preimage_singleton
    (μ := ν) (Finset.univ : Finset (ZMod (2 ^ K)))
    (f := PadicInt.toZModPow K) (fun b _ => measurableSet_padicCylinder K b)
  have hsum' : (∑ b : ZMod (2 ^ K), ν (padicCylinder K b)) = 1 := by
    calc
      _ = ∑ b : ZMod (2 ^ K),
          ν (PadicInt.toZModPow K ⁻¹' ({b} : Set (ZMod (2 ^ K)))) := by
        apply Finset.sum_congr rfl
        intro b _
        congr 1
      _ = ν (PadicInt.toZModPow K ⁻¹'
          (↑(Finset.univ : Finset (ZMod (2 ^ K))) : Set (ZMod (2 ^ K)))) := hsum
      _ = 1 := by simp
  have hmul : ν (padicCylinder K a) * ((2 ^ K : ℕ) : ℝ≥0∞) = 1 := by
    calc
      _ = ((2 ^ K : ℕ) : ℝ≥0∞) * ν (padicCylinder K a) := mul_comm _ _
      _ = ∑ _b : ZMod (2 ^ K), ν (padicCylinder K a) := by
        simp [ZMod.card]
      _ = ∑ b : ZMod (2 ^ K), ν (padicCylinder K b) := by
        apply Finset.sum_congr rfl
        intro b _
        exact add_one_invariant_cylinder_eq hν K a b
      _ = 1 := hsum'
  exact ENNReal.eq_inv_of_mul_eq_one_left hmul

/-- Normalized Haar measure is the unique probability measure invariant under
the 2-adic adding machine. -/
theorem add_one_unique_invariant_probability {ν : Measure ℤ_[2]}
    [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun z : ℤ_[2] => z + 1) ν ν) :
    ν = padicHaar := by
  apply MeasureTheory.ext_of_generate_finite
    {s : Set ℤ_[2] | ∃ K : ℕ, ∃ a : ZMod (2 ^ K), s = padicCylinder K a}
  · exact BorelSpace.measurable_eq.trans
      isTopologicalBasis_padicCylinder.borel_eq_generateFrom
  · exact isPiSystem_padicCylinder
  · rintro _ ⟨K, a, rfl⟩
    rw [add_one_invariant_cylinder hν, padicHaar_padicCylinder]
  · simp

/-- The rational-clock recurrence is uniquely ergodic: normalized Haar measure
is its only invariant probability measure. -/
theorem padicStep_unique_invariant_probability (c : ℕ)
    {ν : Measure ℤ_[2]} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (padicStep c) ν ν) :
    ν = padicHaar := by
  let e : ℤ_[2] ≃ᵐ ℤ_[2] :=
    (padicClockIsometryEquiv c).toHomeomorph.toMeasurableEquiv
  let ν' : Measure ℤ_[2] := Measure.map e.symm ν
  let _ : IsProbabilityMeasure ν' :=
    Measure.isProbabilityMeasure_map e.symm.measurable.aemeasurable
  have he : MeasurePreserving e.symm ν ν' :=
    e.symm.measurable.measurePreserving ν
  have hsemiconj : Semiconj e.symm (padicStep c) (fun z : ℤ_[2] => z + 1) := by
    intro x
    change inversePadicClock c (padicStep c x) = inversePadicClock c x + 1
    rw [padicStep, inversePadicClock_padicClock]
  have hadd : MeasurePreserving (fun z : ℤ_[2] => z + 1) ν' ν' :=
    he.of_semiconj hν hsemiconj (by fun_prop)
  have hν' : ν' = padicHaar := add_one_unique_invariant_probability hadd
  have he' : MeasurePreserving e.symm ν padicHaar := hν' ▸ he
  have hback : MeasurePreserving e padicHaar ν :=
    MeasurePreserving.symm e.symm he'
  calc
    ν = Measure.map e padicHaar := hback.map_eq.symm
    _ = padicHaar := by
      change Measure.map (padicClock c) padicHaar = padicHaar
      exact (padicClock_preserves_haar c).map_eq

/-- Haar measure is ergodic for the rational-clock recurrence. -/
theorem padicStep_ergodic (c : ℕ) : Ergodic (padicStep c) padicHaar := by
  have hadd : Ergodic (fun z : ℤ_[2] => (1 : ℤ_[2]) + z) padicHaar := by
    apply ergodic_add_left_of_denseRange_nsmul
    · simpa only [nsmul_eq_mul, mul_one] using PadicInt.denseRange_natCast (p := 2)
  let e : ℤ_[2] ≃ᵐ ℤ_[2] :=
    (padicClockIsometryEquiv c).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e padicHaar padicHaar :=
    padicClock_preserves_haar c
  have := (he.ergodic_conjugate_iff
    (f := fun z : ℤ_[2] => (1 : ℤ_[2]) + z)).mpr hadd
  change Ergodic
    (fun x => padicClock c ((1 : ℤ_[2]) + inversePadicClock c x)) padicHaar at this
  have hfun : (fun x => padicClock c ((1 : ℤ_[2]) + inversePadicClock c x)) =
      padicStep c := by
    funext x
    rw [padicStep]
    congr 1
    exact add_comm _ _
  rw [hfun] at this
  exact this

/-- Consolidated quantitative endpoint. -/
theorem padicClockQuantitativeTheory :
    (∀ (c K : ℕ) (x : ℤ_[2]) (a : ZMod (2 ^ K)),
      ∃! n : Fin (2 ^ K),
        PadicInt.toZModPow K ((padicStep c)^[n.1] x) = a) ∧
    (∀ c : ℕ, MeasurePreserving (padicClock c) padicHaar padicHaar) ∧
    (∀ c : ℕ, MeasurePreserving (padicStep c) padicHaar padicHaar) ∧
    (∀ c : ℕ, Ergodic (padicStep c) padicHaar) ∧
    (∀ (c : ℕ) (ν : Measure ℤ_[2]), IsProbabilityMeasure ν →
      MeasurePreserving (padicStep c) ν ν → ν = padicHaar) := by
  refine ⟨padicStep_residue_existsUnique, padicClock_preserves_haar,
    padicStep_preserves_haar, padicStep_ergodic, ?_⟩
  intro c ν hprob hpres
  let _ := hprob
  exact padicStep_unique_invariant_probability c hpres

end RationalClockResearch

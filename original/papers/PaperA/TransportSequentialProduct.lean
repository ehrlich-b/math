import PaperA.Definitions

/-! Conjugation of an effect-guarded sequential product by a fixed unital
Jordan automorphism. No covariance of the original product is assumed.
The globalization theorem is a consumer of two explicitly supplied equalities. -/
noncomputable section
open EuclideanJordan
namespace PaperA.TransportSequentialProduct

variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J]

theorem symm_auto (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) : JordanAuto g.symm := by
  constructor
  · apply g.injective
    simpa using hg.1.symm
  · intro x y
    apply g.injective
    simp only [g.apply_symm_apply, hg.2]

theorem positive_iff (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) (a : J) :
    Positive (g a) ↔ Positive a := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨g.symm x, g.injective ?_⟩
    simpa only [hg.2, g.apply_symm_apply] using hx
  · rintro ⟨x, rfl⟩
    exact ⟨g x, (hg.2 x x).symm⟩

theorem below_iff (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) (a b : J) :
    Below (g a) (g b) ↔ Below a b := by
  unfold Below
  simpa only [map_sub] using positive_iff g hg (b-a)

theorem effect_iff (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) (a : J) :
    IsEffect (g a) ↔ IsEffect a := by
  exact and_congr (positive_iff g hg a)
    (by simpa only [hg.1] using below_iff g hg a 1)

theorem ouNorm_map (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) (a : J) :
    ouNorm (g a) = ouNorm a := by
  unfold ouNorm
  congr 1
  ext r
  change (0 ≤ r ∧ Below (-r • (1 : J)) (g a) ∧ Below (g a) (r • (1 : J))) ↔
    (0 ≤ r ∧ Below (-r • (1 : J)) a ∧ Below a (r • (1 : J)))
  simpa only [g.map_smul, hg.1] using
    and_congr (Iff.rfl : (0 ≤ r) ↔ (0 ≤ r))
      (and_congr (below_iff g hg (-r • (1 : J)) a) (below_iff g hg a (r • (1 : J))))

/-- The order-unit distance is preserved without using any topology bridge. -/
theorem ouNorm_sub_map (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) (a b : J) :
    ouNorm (g a - g b) = ouNorm (a - b) := by
  simpa only [map_sub] using ouNorm_map g hg (a-b)

variable [FiniteDimensional ℝ J]

/-- Every operational field is pulled back along the same linear equivalence. -/
def transport (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) (P : SequentialProduct J) :
    SequentialProduct J where
  sp a b := g.symm (P.sp (g a) (g b))
  closed a b ha hb :=
    (effect_iff g.symm (symm_auto g hg) _).mpr
      (P.closed _ _ ((effect_iff g hg a).mpr ha) ((effect_iff g hg b).mpr hb))
  S1 a b c ha hb hc hbc := by
    apply g.injective
    simp only [g.apply_symm_apply, g.map_add]
    exact P.S1 _ _ _ ((effect_iff g hg a).mpr ha) ((effect_iff g hg b).mpr hb)
      ((effect_iff g hg c).mpr hc)
      (by simpa only [g.map_add] using (effect_iff g hg (b+c)).mpr hbc)
  S2 b hb a ha ε hε := by
    obtain ⟨δ, hδ, h⟩ := P.S2 (g b) ((effect_iff g hg b).mpr hb)
      (g a) ((effect_iff g hg a).mpr ha) ε hε
    refine ⟨δ, hδ, fun a' ha' hdist => ?_⟩
    rw [ouNorm_sub_map g.symm (symm_auto g hg)]
    apply h (g a') ((effect_iff g hg a').mpr ha')
    rwa [ouNorm_sub_map g hg]
  S3 a ha := by
    apply g.injective
    simp only [g.apply_symm_apply, hg.1]
    exact P.S3 _ ((effect_iff g hg a).mpr ha)
  S4 a b ha hb hab := by
    apply g.injective
    have h : P.sp (g a) (g b) = 0 := by
      simpa only [g.apply_symm_apply, g.map_zero] using congrArg g hab
    simpa only [g.apply_symm_apply, g.map_zero] using
      P.S4 _ _ ((effect_iff g hg a).mpr ha) ((effect_iff g hg b).mpr hb) h
  S5 a b c ha hb hc hab := by
    apply g.injective
    have h : Compatible P.sp (g a) (g b) := by
      simpa only [Compatible, g.apply_symm_apply] using congrArg g hab
    simp only [g.apply_symm_apply]
    exact P.S5 _ _ _ ((effect_iff g hg a).mpr ha) ((effect_iff g hg b).mpr hb)
      ((effect_iff g hg c).mpr hc) h
  S6_compl a b ha hb hab := by
    -- Work in the image coordinates, where the original complement law applies.
    have h : Compatible P.sp (g a) (g b) := by
      simpa only [Compatible, g.apply_symm_apply] using congrArg g hab
    change g.symm (P.sp (g a) (g (1-b))) = g.symm (P.sp (g (1-b)) (g a))
    rw [map_sub g, hg.1]
    exact congrArg g.symm (P.S6_compl _ _ ((effect_iff g hg a).mpr ha)
      ((effect_iff g hg b).mpr hb) h)
  S6_sum a b c ha hb hc hbc hab hac := by
    have hab' : Compatible P.sp (g a) (g b) := by
      simpa only [Compatible, g.apply_symm_apply] using congrArg g hab
    have hac' : Compatible P.sp (g a) (g c) := by
      simpa only [Compatible, g.apply_symm_apply] using congrArg g hac
    change g.symm (P.sp (g a) (g (b+c))) = g.symm (P.sp (g (b+c)) (g a))
    rw [g.map_add]
    exact congrArg g.symm (P.S6_sum _ _ _ ((effect_iff g hg a).mpr ha)
      ((effect_iff g hg b).mpr hb) ((effect_iff g hg c).mpr hc)
      (by simpa only [← g.map_add] using (effect_iff g hg (b+c)).mpr hbc) hab' hac')
  S7 a b c ha hb hc hab hac := by
    have hab' : Compatible P.sp (g a) (g b) := by
      simpa only [Compatible, g.apply_symm_apply] using congrArg g hab
    have hac' : Compatible P.sp (g a) (g c) := by
      simpa only [Compatible, g.apply_symm_apply] using congrArg g hac
    change g.symm (P.sp (g a) (g (g.symm (P.sp (g b) (g c))))) =
      g.symm (P.sp (g (g.symm (P.sp (g b) (g c)))) (g a))
    simp only [g.apply_symm_apply]
    exact congrArg g.symm (P.S7 _ _ _ ((effect_iff g hg a).mpr ha)
      ((effect_iff g hg b).mpr hb) ((effect_iff g hg c).mpr hc) hab' hac')

theorem transport_sp (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) (P : SequentialProduct J)
    (a b : J) : (transport g hg P).sp a b = g.symm (P.sp (g a) (g b)) := rfl

/-- Pull back a supplied standard-frame identity, with comparison covariance
supplied separately. Effect guards match the intended consumer; no classification
or diagonalization witness is constructed by this implication. -/
theorem conditional_globalization (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g)
    (P : SequentialProduct J) (tq : J → J → J) (a b : J)
    (_ha : IsEffect a) (_hb : IsEffect b)
    (hdiag : (transport g hg P).sp (g.symm a) (g.symm b) = tq (g.symm a) (g.symm b))
    (htq : tq (g.symm a) (g.symm b) = g.symm (tq a b)) : P.sp a b = tq a b := by
  apply g.symm.injective
  simpa only [transport_sp, g.apply_symm_apply] using hdiag.trans htq

end PaperA.TransportSequentialProduct

import PaperA.Definitions

noncomputable section
open EuclideanJordan
namespace PaperA
variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J]

theorem strict_effect_density_aux (a : J) (ha : IsEffect a) : (∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsEffect ((1-ε) • a+ε • (1 : J)) ∧ StrictPositive ((1-ε) • a+ε • (1 : J))) ∧ Filter.Tendsto (fun ε : ℝ => (1-ε) • a+ε • (1 : J)) (nhds 0) (nhds a) := by
  have hc (x : J) : IsSoS (jmulₗ J) x ↔ Positive x := by
    rw [isSoS_iff_exists_sq (jmulₗ_comm (J := J)) jmulₗ_jordan jmulₗ_formallyReal jmulₗ_inner_assoc (1 : J) jmulₗ_one_mul]
    constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, hy.symm⟩
  have hscale {r : ℝ} (hr : 0 ≤ r) {x : J} (hx : Positive x) : Positive (r • x) :=
    (hc _).mp (((hc _).mpr hx).smul hr)
  have hadd {x y : J} (hx : Positive x) (hy : Positive y) : Positive (x + y) :=
    (hc _).mp (((hc _).mpr hx).add ((hc _).mpr hy))
  have hone : Positive (1 : J) := ⟨1, EuclideanJordanAlgebra.one_mul 1⟩
  constructor
  · intro ε hε hε1
    have h0 : 0 ≤ 1 - ε := sub_nonneg.mpr hε1
    have hpos := hscale h0 ha.1
    have hunit := hscale (le_of_lt hε) hone
    have hcomp := hscale h0 ha.2
    refine ⟨⟨hadd hpos hunit, ?_⟩, ⟨ε, hε, ?_⟩⟩
    · change Positive (1 - ((1 - ε) • a + ε • (1 : J)))
      have heq : (1 : J) - ((1 - ε) • a + ε • (1 : J)) = (1 - ε) • ((1 : J) - a) := by
        module
      rw [heq]
      exact hcomp
    · change Positive ((1 - ε) • a + ε • (1 : J) - ε • (1 : J))
      simpa using hpos
  · have h : Continuous (fun ε : ℝ => (1-ε) • a+ε • (1 : J)) := by fun_prop
    simpa using (h.continuousAt (x := (0 : ℝ))).tendsto
end PaperA

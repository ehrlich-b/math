import Mathlib.Analysis.InnerProductSpace.PiL2
import Lean.Util.CollectAxioms

noncomputable section
namespace PaperA
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
structure AxisField (d : ℕ) where
  A : Vec d → (Vec d →L[ℝ] Vec d)
  continuous : ContinuousOn A {v | ‖v‖ = 1}
  skew : ∀ v, ‖v‖ = 1 → ∀ x y, inner ℝ x (A v y) = -inner ℝ (A v x) y
  fixes : ∀ v, ‖v‖ = 1 → A v v = 0
  odd : ∀ v, ‖v‖ = 1 → A (-v) = -A v
end PaperA

namespace PaperA

/-- Restrict a vector to its first three coordinates (indices 0, 1, 2). -/
def v4Projection : Vec 4 →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v i := v i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The alternating three-form e₁* ∧ e₂* ∧ e₃* on real Euclidean four-space. -/
def v4Omega : AlternatingMap ℝ (Vec 4) ℝ (Fin 3) :=
  Matrix.detRowAlternating.compLinearMap v4Projection

/-- The explicit determinant formula, using zero-based coordinate indices. -/
theorem v4Omega_coordinates (v x y : Vec 4) :
    v4Omega ![v, x, y] =
      v 0 * (x 1 * y 2 - x 2 * y 1) -
      v 1 * (x 0 * y 2 - x 2 * y 0) +
      v 2 * (x 0 * y 1 - x 1 * y 0) := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun i j => v4Projection (![v, x, y] i) j
  change M.det = _
  rw [Matrix.det_fin_three]
  change v 0 * x 1 * y 2 - v 0 * x 2 * y 1 - v 1 * x 0 * y 2 +
    v 1 * x 2 * y 0 + v 2 * x 0 * y 1 - v 2 * x 1 * y 0 = _
  ring

/-- Coordinate matrix unit: y ↦ yⱼeᵢ. -/
def v4RankOne (i j : Fin 4) : Vec 4 →L[ℝ] Vec 4 :=
  (EuclideanSpace.proj j).smulRight (EuclideanSpace.single i 1)

/-- The operator determined by ⟨x, A(v)y⟩ = omega(v,x,y). -/
def v4Operator (v : Vec 4) : Vec 4 →L[ℝ] Vec 4 :=
  v 2 • v4RankOne 0 1 - v 1 • v4RankOne 0 2 +
  v 0 • v4RankOne 1 2 - v 2 • v4RankOne 1 0 +
  v 1 • v4RankOne 2 0 - v 0 • v4RankOne 2 1

@[simp] theorem v4Operator_coord0 (v y : Vec 4) :
    (v4Operator v y) 0 = v 2 * y 1 - v 1 * y 2 := by
  simp [v4Operator, v4RankOne]

@[simp] theorem v4Operator_coord1 (v y : Vec 4) :
    (v4Operator v y) 1 = v 0 * y 2 - v 2 * y 0 := by
  simp [v4Operator, v4RankOne]

@[simp] theorem v4Operator_coord2 (v y : Vec 4) :
    (v4Operator v y) 2 = v 1 * y 0 - v 0 * y 1 := by
  simp [v4Operator, v4RankOne]

@[simp] theorem v4Operator_coord3 (v y : Vec 4) :
    (v4Operator v y) 3 = 0 := by
  simp [v4Operator, v4RankOne]

theorem v4_inner_identity (v x y : Vec 4) :
    inner ℝ x (v4Operator v y) = v4Omega ![v, x, y] := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, v4Omega_coordinates]
  ring

/-- Continuity in the operator norm, on all of R⁴. -/
theorem v4Operator_continuous : Continuous v4Operator := by
  unfold v4Operator
  exact (((((EuclideanSpace.proj (𝕜 := ℝ) 2).continuous.smul continuous_const).sub
    ((EuclideanSpace.proj (𝕜 := ℝ) 1).continuous.smul continuous_const)).add
    ((EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.smul continuous_const)).sub
    ((EuclideanSpace.proj (𝕜 := ℝ) 2).continuous.smul continuous_const)).add
    ((EuclideanSpace.proj (𝕜 := ℝ) 1).continuous.smul continuous_const) |>.sub
    ((EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.smul continuous_const)

theorem v4Operator_skew (v x y : Vec 4) :
    inner ℝ x (v4Operator v y) = -inner ℝ (v4Operator v x) y := by
  rw [real_inner_comm y (v4Operator v x), v4_inner_identity, v4_inner_identity,
    v4Omega_coordinates, v4Omega_coordinates]
  ring

theorem v4Operator_fixes (v : Vec 4) : v4Operator v v = 0 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp <;> ring

theorem v4Operator_odd (v : Vec 4) : v4Operator (-v) = -v4Operator v := by
  apply ContinuousLinearMap.ext
  intro y
  apply PiLp.ext
  intro i
  fin_cases i <;> simp <;> ring

/-- Every output lies in the tangent hyperplane to the sphere at a unit axis. -/
theorem v4Operator_tangent (v y : Vec 4) : inner ℝ v (v4Operator v y) = 0 := by
  rw [v4_inner_identity, v4Omega_coordinates]
  ring

/-- The concrete nonzero tangent-skew field on the unit sphere in R⁴. -/
def v4Field : AxisField 4 where
  A := v4Operator
  continuous := v4Operator_continuous.continuousOn
  skew v _ x y := v4Operator_skew v x y
  fixes v _ := v4Operator_fixes v
  odd v _ := v4Operator_odd v

/-- The first standard unit vector, e₁ in manuscript notation. -/
def v4Witness : Vec 4 := EuclideanSpace.single 0 1

theorem v4Witness_unit : ‖v4Witness‖ = 1 := by
  simp [v4Witness]

/-- At the witness, A(e₁)e₂ = -e₃, including all four coordinates. -/
theorem v4Witness_evaluation :
    v4Field.A v4Witness (EuclideanSpace.single 1 1) =
      -EuclideanSpace.single 2 1 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [v4Field, v4Witness]

theorem v4Field_nonzero : v4Field.A v4Witness ≠ 0 := by
  intro h
  have he := congrArg
    (fun T : Vec 4 →L[ℝ] Vec 4 => (T (EuclideanSpace.single 1 1)) 2) h
  simp [v4Field, v4Witness] at he

/-- The defining alternating three-form is itself nonzero. -/
theorem v4Omega_nonzero : v4Omega ≠ 0 := by
  intro h
  have he := congrArg (fun f : AlternatingMap ℝ (Vec 4) ℝ (Fin 3) =>
    f ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1,
      EuclideanSpace.single 2 1]) h
  simp [v4Omega_coordinates] at he

end PaperA

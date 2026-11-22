import PaperA.Definitions

noncomputable section
namespace PaperA

private def rankOne {d : ℕ} (i j : Fin d) : Vec d →L[ℝ] Vec d :=
  (EuclideanSpace.proj j).smulRight (EuclideanSpace.single i 1)

private def op {d : ℕ} (i j k : Fin d) (v : Vec d) : Vec d →L[ℝ] Vec d :=
  v k • rankOne i j - v j • rankOne i k + v i • rankOne j k -
  v k • rankOne j i + v j • rankOne k i - v i • rankOne k j

private theorem op_cont {d : ℕ} (i j k : Fin d) : Continuous (op i j k) := by
  unfold op
  fun_prop

private theorem op_fixes {d : ℕ} (i j k : Fin d) (v : Vec d) : op i j k v v = 0 := by
  apply PiLp.ext
  intro a
  simp [op, rankOne]
  ring

private theorem op_odd {d : ℕ} (i j k : Fin d) (v : Vec d) : op i j k (-v) = -op i j k v := by
  ext y a
  simp [op, rankOne]
  ring

private theorem op_skew {d : ℕ} (i j k : Fin d) (v x y : Vec d) :
    inner ℝ x (op i j k v y) = -inner ℝ (op i j k v x) y := by
  simp [op, rankOne, inner_add_right, inner_sub_right, inner_add_left, inner_sub_left,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm, EuclideanSpace.inner_single_right]
  ring

theorem higherSpinNonzero (d : ℕ) (hd : 3 ≤ d) : ∃ A : AxisField d, ∃ v, ‖v‖ = 1 ∧ A.A v ≠ 0 := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  let k : Fin d := ⟨2, by omega⟩
  let A : AxisField d := ⟨op i j k, (op_cont i j k).continuousOn,
    fun v _ x y => op_skew i j k v x y, fun v _ => op_fixes i j k v,
    fun v _ => op_odd i j k v⟩
  refine ⟨A, EuclideanSpace.single i 1, by simp, ?_⟩
  intro h
  have he := congrArg (fun T : Vec d →L[ℝ] Vec d => (T (EuclideanSpace.single j 1)) k) h
  simp [A, op, rankOne, i, j, k] at he
end PaperA

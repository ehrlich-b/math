import PaperA.Assembly
open scoped BigOperators
open EuclideanJordan
noncomputable section
namespace PaperA
variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J]
theorem detection_eigen_roots (M : ComplexModel J 2) (a : J) (r : ℝ) (ha : M.map a = !![(Real.exp (-r) : ℂ), 0; 0, 1])
    (i : Fin (resolve a).n) :
    (resolve a).eigenvalue i = Real.exp (-r) ∨ (resolve a).eigenvalue i = 1 := by
  have heig : a * (resolve a).frame.p i = (resolve a).eigenvalue i • (resolve a).frame.p i := by
    nth_rw 1 [(resolve a).equation]
    rw [Finset.sum_mul, Finset.sum_eq_single i]
    · rw [smul_mul_assoc, (resolve a).frame.orthIdem.idem i]
    · intro j hj hji
      rw [smul_mul_assoc, (resolve a).frame.orthIdem.orth j i hji, smul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hm := M.product a ((resolve a).frame.p i)
  rw [heig, map_smul, ha] at hm
  have hp := M.product ((resolve a).frame.p i) ((resolve a).frame.p i)
  rw [(resolve a).frame.orthIdem.idem i] at hp
  have hn : M.map ((resolve a).frame.p i) ≠ 0 := by
    intro h
    apply (resolve a).frame.primitive i |>.ne_zero
    apply M.injective
    simpa using h
  have hm00 := congrFun (congrFun hm 0) 0
  have hm11 := congrFun (congrFun hm 1) 1
  have hp01 := congrFun (congrFun hp 0) 1
  have hp10 := congrFun (congrFun hp 1) 0
  simp [rawMatMul, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] at hm00 hm11 hp01 hp10
  by_contra hh
  push_neg at hh
  have h0 : (M.map ((resolve a).frame.p i)) 0 0 = 0 := by
    have hne : ((resolve a).eigenvalue i : ℂ) - (Real.exp (-r) : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hh.1)
    apply (mul_eq_zero.mp (show (((resolve a).eigenvalue i : ℂ) - (Real.exp (-r) : ℂ)) * M.map ((resolve a).frame.p i) 0 0 = 0 by
      rw [Complex.ofReal_exp]; push_cast
      linear_combination hm00)).resolve_left hne
  have h1 : (M.map ((resolve a).frame.p i)) 1 1 = 0 := by
    have hne : ((resolve a).eigenvalue i : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hh.2)
    apply (mul_eq_zero.mp (show (((resolve a).eigenvalue i : ℂ) - 1) * M.map ((resolve a).frame.p i) 1 1 = 0 by
      linear_combination hm11)).resolve_left hne
  have h01 : (M.map ((resolve a).frame.p i)) 0 1 = 0 := by simpa [h0, h1] using hp01
  have h10 : (M.map ((resolve a).frame.p i)) 1 0 = 0 := by simpa [h0, h1] using hp10
  apply hn
  ext x y
  fin_cases x <;> fin_cases y <;> first | exact h0 | exact h01 | exact h10 | exact h1

theorem detection_cfc (M : ComplexModel J 2) (a : J) (f : ℝ → ℝ) (r : ℝ)
    (hr : 0 < r) (ha : M.map a = !![(Real.exp (-r) : ℂ), 0; 0, 1]) :
    M.map (PaperA.cfc f a) = !![((f (Real.exp (-r))) : ℂ), 0; 0, ((f 1) : ℂ)] := by
  let d := Real.exp (-r)
  let u := (f d - f 1) / (d - 1)
  let v := f 1 - u
  have hd : d ≠ 1 := by
    dsimp [d]
    exact ne_of_lt (Real.exp_lt_one_iff.mpr (by linarith))
  have hf (i : Fin (resolve a).n) : f ((resolve a).eigenvalue i) = u * ((resolve a).eigenvalue i) + v := by
    rcases detection_eigen_roots M a r ha i with hi | hi
    · change (resolve a).eigenvalue i = d at hi
      rw [hi]
      dsimp [u, v]
      field_simp
      ring
    · rw [hi]
      dsimp [v]
      ring
  have hc : PaperA.cfc f a = u • a + v • (1 : J) := by
    unfold PaperA.cfc
    simp_rw [hf, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [← (resolve a).equation, (resolve a).frame.complete]
  have huv : u * d + v = f d := by
    dsimp [u, v]
    field_simp
    ring
  rw [hc, map_add, map_smul, map_smul, ha]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, M.unit, v, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub, ← huv, d]
  push_cast
  ring

end PaperA

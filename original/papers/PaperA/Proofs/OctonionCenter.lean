import PaperA.Octonion
import Lean.Util.CollectAxioms

noncomputable section
namespace PaperA

theorem octonion_center (γ : Oct) (him : γ.1.re = 0)
    (hc : ∀ x, octMul γ x = octMul x γ) : γ = 0 := by
  rcases γ with ⟨a, b⟩
  have h01 := hc (0, (1 : Quaternion ℝ))
  have hbconj : b = star b := by
    have h := congrArg Prod.fst h01
    simpa [octMul] using h
  have haconj : a = star a := by
    have h := congrArg Prod.snd h01
    simpa [octMul] using h
  have ha : a = 0 := by
    have hreal : a = (a.re : Quaternion ℝ) := (Quaternion.star_eq_self).mp haconj.symm
    rw [hreal, him]
    simp
  let qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  have hstarqi : star qi = -qi := by
    change star (⟨0, 1, 0, 0⟩ : Quaternion ℝ) = -⟨0, 1, 0, 0⟩
    rw [QuaternionAlgebra.star_mk]
    ext <;> norm_num
  have hI := hc (qi, 0)
  have hbi : b * qi = -(b * qi) := by
    have h' : b * star qi = b * qi := by
      have h := congrArg Prod.snd hI
      simpa [octMul, ha, qi] using h
    calc
      b * qi = b * star qi := h'.symm
      _ = -(b * qi) := by rw [hstarqi]; simp
  have hbi0 : b * qi = 0 := by
    have hsum : b * qi + b * qi = 0 := by
      have h := congrArg (fun y : Quaternion ℝ => b * qi + y) hbi
      simpa using h
    have hdouble : (2 : Quaternion ℝ) * (b * qi) = 0 := by
      simpa [two_mul] using hsum
    exact (mul_eq_zero.mp hdouble).resolve_left (by
      intro h
      have hr := congrArg (fun q : Quaternion ℝ => q.re) h
      change (2 : ℝ) = 0 at hr
      norm_num at hr)
  have hb : b = 0 := (mul_eq_zero.mp hbi0).resolve_right (by
    intro h
    have hi := congrArg (fun q : Quaternion ℝ => q.imI) h
    change qi.imI = 0 at hi
    norm_num [qi] at hi)
  simp [ha, hb]
end PaperA

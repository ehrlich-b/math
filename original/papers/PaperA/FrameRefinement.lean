import EuclideanJordan.FrameExists

noncomputable section
open scoped BigOperators
open EuclideanJordan

namespace PaperA
variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J]

/-- Every nonzero idempotent is a sum of ambient primitive idempotents
    which belong to its Peirce-one subalgebra. -/
theorem idempotent_has_primitive_frame {c : J} (hc : c * c = c) (hc0 : c ≠ 0) :
    ∃ (n : ℕ) (p : Fin n → J), IsOrthIdemFamily p ∧ (∀ i, IsPrimitive (p i)) ∧
      (∀ i, c * p i = p i) ∧ (∑ i, p i) = c := by
  have hu : (1 : ↥(peirceOneSub hc)) ≠ 0 := by
    intro h
    apply hc0
    have h' := congrArg Subtype.val h
    simpa only [coe_one_peirceOneSub, ZeroMemClass.coe_zero] using h'
  obtain ⟨n, ⟨F⟩⟩ := exists_jordanFrame ↥(peirceOneSub hc) hu
  refine ⟨n, fun i => (F.p i : J), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i
    exact congrArg Subtype.val (F.orthIdem.idem i)
  · intro i j hij
    exact congrArg Subtype.val (F.orthIdem.orth i j hij)
  · intro i
    exact isPrimitive_coe_of_peirceOne hc (F.primitive i)
  · intro i
    exact (F.p i).property
  · rw [← AddSubmonoidClass.coe_finsetSum, F.complete]
    exact coe_one_peirceOneSub hc
end PaperA

namespace PaperA
variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J]

theorem primitive_spectral_frame (a : J) :
    ∃ (n : ℕ) (F : JordanFrame J n) (lam : Fin n → ℝ),
      a = ∑ i, lam i • F.p i := by
  classical
  obtain ⟨m, q, l, hq, hsum, ha⟩ := spectral_resolution_complete' a
  have pieces (i : Fin m) : ∃ (n : ℕ) (p : Fin n → J),
      IsOrthIdemFamily p ∧ (∀ k, IsPrimitive (p k)) ∧
      (∀ k, q i * p k = p k) ∧ (∑ k, p k) = q i := by
    by_cases hi : q i = 0
    · refine ⟨0, Fin.elim0, ⟨(fun k => Fin.elim0 k), ?_⟩, (fun k => Fin.elim0 k), (fun k => Fin.elim0 k), ?_⟩
      · intro k; exact Fin.elim0 k
      · simp [hi]
    · exact idempotent_has_primitive_frame (hq.idem i) hi
  choose n p hp hprim hone htotal using pieces
  let I := Σ i : Fin m, Fin (n i)
  let r : I → J := fun t => p t.1 t.2
  have hr : IsOrthIdemFamily r := by
    constructor
    · intro t; exact (hp t.1).idem t.2
    · intro s t hst
      obtain ⟨i, k⟩ := s
      obtain ⟨j, v⟩ := t
      by_cases h : i = j
      · subst j
        exact (hp i).orth k v (by intro e; apply hst; cases e; rfl)
      · have hz : q i * p j v = 0 := by
          have h1 := eigen_one_mul_zero (hq.idem j) (hone j v)
            (hq.orth j i (Ne.symm h))
          simpa only [mul_comm] using h1
        exact eigen_one_mul_zero (hq.idem i) (hone i k) hz
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, ⟨fun i => r (e i), ?_, ?_, ?_⟩, fun i => l (e i).1, ?_⟩
  · exact ⟨fun i => hr.idem (e i), fun i j hij => hr.orth (e i) (e j) (fun h => hij (e.injective h))⟩
  · intro i; exact hprim (e i).1 (e i).2
  · rw [Equiv.sum_comp e]
    rw [Fintype.sum_sigma]
    simp only [r, htotal, hsum]
  · change a = ∑ i, l (e i).1 • r (e i)
    calc
      a = ∑ i, l i • q i := ha
      _ = ∑ t : I, l t.1 • r t := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← htotal i, Finset.smul_sum]
      _ = ∑ i, l (e i).1 • r (e i) := (Equiv.sum_comp e (fun t => l t.1 • r t)).symm

end PaperA

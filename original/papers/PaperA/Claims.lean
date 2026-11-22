import PaperA.Lib.Early.SpinGeneratorBound
import PaperA.Lib.Early.HigherSpinCovariance
import PaperA.Lib.Early.SpinTransport
import PaperA.Lib.Early.SpinCompatibility
import PaperA.Lib.Early.SimpleDecomposition
import PaperA.Lib.Early.QubitField
import PaperA.Lib.Early.SpinS2
import PaperA.Lib.Early.dynamical_matrix
import PaperA.Lib.Early.jordan_transport
import PaperA.Lib.Early.strict_effect_density
import PaperA.Lib.Early.HigherSpinNonzero
import PaperA.Lib.Early.derivations_exponentiate
import PaperA.Lib.Early.ComplexStructureExp
import PaperA.Lib.Early.FrameBlocks
import PaperA.PhysicsDefinitions
import PaperA.Lib.Early.DetectionSpecialization
import Mathlib.Analysis.Calculus.FDeriv.Basic

noncomputable section
open scoped BigOperators
open EuclideanJordan
namespace PaperA
variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J]

/-- square_cone_selfdual: §2.1; F2. The cone of squares is self-dual. -/
theorem square_cone_selfdual (a : J) : Positive a ↔ ∀ b : J, Positive b → 0 ≤ inner ℝ a b := by
  classical
  have hcone (x : J) : Positive x ↔ IsSoS (jmulₗ J) x := by
    have h := isSoS_iff_exists_sq (jmulₗ_comm (J := J)) jmulₗ_jordan
      jmulₗ_formallyReal jmulₗ_inner_assoc (1 : J) jmulₗ_one_mul x
    constructor
    · rintro ⟨y, hy⟩
      exact h.mpr ⟨y, hy.symm⟩
    · intro hx
      obtain ⟨y, hy⟩ := h.mp hx
      exact ⟨y, hy.symm⟩
  obtain ⟨n, q, lam, hfam, _hsum, ha⟩ := spectral_resolution_complete' a
  have hidem : ∀ i, jmulₗ J (q i) (q i) = q i := hfam.idem
  have horth : ∀ i j, i ≠ j → jmulₗ J (q i) (q j) = 0 := hfam.orth
  constructor
  · intro hapos b hb
    obtain ⟨y, rfl⟩ := hb
    rw [ha, sum_inner]
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : q i = 0
    · simp [hi]
    · rw [real_inner_smul_left]
      apply mul_nonneg
      · exact nonneg_coeff_of_isSoS (jmulₗ_comm (J := J)) jmulₗ_jordan
          jmulₗ_inner_assoc hidem horth ha ((hcone a).mp hapos) hi
      · rw [← EuclideanJordanAlgebra.inner_assoc']
        exact inner_mul_self_nonneg_of_idem (jmulₗ_comm (J := J)) jmulₗ_jordan
          jmulₗ_inner_assoc (hidem i) y
  · intro hdual
    apply (hcone a).mpr
    rw [ha]
    apply isSoS_sum
    intro i _
    by_cases hi : q i = 0
    · rw [hi, smul_zero]
      exact isSoS_zero
    · apply isSoS_smul_idem (m := jmulₗ J) _ (hidem i)
      apply nonneg_coeff_of_inner_nonneg jmulₗ_inner_assoc hidem horth ha hi
      rw [real_inner_comm]
      exact hdual (q i) ⟨q i, hfam.idem i⟩

/-- trace_faithful: §2.1; F2. A positive element paired with the unit vanishes only at zero; this suffices for the trace argument. -/
theorem trace_faithful (a : J) (ha : Positive a) : inner ℝ a (1 : J) = 0 ↔ a = 0 := by
  rcases ha with ⟨x, rfl⟩
  constructor
  · intro h
    have hu : x * (1 : J) = x := by
      first
      | exact EuclideanJordanAlgebra.one_mul x
      | exact (EuclideanJordanAlgebra.mul_comm x (1 : J)).trans
          (EuclideanJordanAlgebra.one_mul x)
    have hi := EuclideanJordanAlgebra.inner_assoc x x (1 : J)
    rw [hu] at hi
    have hx : inner ℝ x x = 0 := hi.symm.trans h
    have hx0 : x = 0 := inner_self_eq_zero.mp hx
    simp [hx0]
  · intro h
    rw [h]
    simp

/-- spectral_frame: §2.1; F1. Every element has a primitive-frame spectral resolution. -/
theorem spectral_frame (a : J) : Nonempty (Resolution a) := by
  exact ⟨resolve a⟩

/-- frame_rank: §2.1. Every Jordan frame has cardinality equal to rank. -/
theorem frame_rank {n : ℕ} (F : JordanFrame J n) : n = EuclideanJordan.rank J := by
  sorry

/-- frame_conjugacy: §2.1; F5. Frames in a simple EJA are conjugate, allowing a permutation. -/
theorem frame_conjugacy (hJ : Simple J) {n : ℕ} (F G : JordanFrame J n) : ∃ g : J ≃ₗ[ℝ] J, JordanAuto g ∧ ∃ σ : Equiv.Perm (Fin n), ∀ i, g (F.p i) = G.p (σ i) := by
  sorry

/-- peirce_decomposition: §2.1. The three Peirce eigenspaces span at an idempotent. -/
theorem peirce_decomposition (p : J) (hp : Idempotent p) (x : J) : ∃ x₀ x₁ x₂ : J, x = x₀+x₁+x₂ ∧ x₀ ∈ Peirce p 0 ∧ x₁ ∈ Peirce p (1/2) ∧ x₂ ∈ Peirce p 1 := by
  obtain ⟨a, b, c, ha, hb, hc, h⟩ := exists_peirce_decomposition hp x
  refine ⟨c, b, a, ?_, ?_, ?_, ?_⟩
  · simpa [add_comm, add_left_comm, add_assoc] using h
  · simpa [Peirce] using hc
  · simpa [Peirce, one_div] using hb
  · simpa [Peirce] using ha

/-- peirce_zero_product: §2.1; F1. The Peirce 1 and 0 subalgebras multiply to zero. -/
theorem peirce_zero_product (p x y : J) (hp : Idempotent p) (hx : x ∈ Peirce p 1) (hy : y ∈ Peirce p 0) : x*y = 0 := by
  apply eigen_one_mul_zero hp
  · simpa [Peirce] using hx
  · simpa [Peirce] using hy

/-- peirce_corner_spectral: §2.1; coalescence proof. A Peirce corner admits a spectral COS summing to its idempotent. -/
theorem peirce_corner_spectral (p y : J) (hp : Idempotent p) (hy : p*y = y) : ∃ n : ℕ, ∃ f : Fin n → J, ∃ lam : Fin n → ℝ, (∀ i, Idempotent (f i)) ∧ (∀ i j, i ≠ j → f i*f j = 0) ∧ (∑ i, f i) = p ∧ y = ∑ i, lam i • f i := by
  classical
  letI : Mul ↥(peirceOneSub hp) := instMulPeirceOneSub hp
  letI : One ↥(peirceOneSub hp) := instOnePeirceOneSub hp
  letI : EuclideanJordanAlgebra ↥(peirceOneSub hp) := instEJAPeirceOneSub hp
  obtain ⟨n, f, lam, hf, hs, hy'⟩ :=
    spectral_resolution_complete' (J := ↥(peirceOneSub hp)) ⟨y, hy⟩
  refine ⟨n, fun i => (f i : J), lam, ?_, ?_, ?_, ?_⟩
  · intro i
    exact congrArg (fun z : ↥(peirceOneSub hp) => (z : J)) (hf.idem i)
  · intro i j hij
    have h := congrArg (fun z : ↥(peirceOneSub hp) => (z : J)) (hf.orth i j hij)
    change (f i : J) * (f j : J) = 0 at h
    exact h
  · have h := congrArg (fun z : ↥(peirceOneSub hp) => (z : J)) hs
    simp only [Submodule.coe_sum] at h
    change (∑ i, (f i : J)) = p at h
    exact h
  · simpa using congrArg (fun z : ↥(peirceOneSub hp) => (z : J)) hy'

/-- frame_peirce_span: eq:peirce. Diagonal atoms and off-diagonal Peirce blocks span J. -/
theorem frame_peirce_span {n : ℕ} (F : JordanFrame J n) : Submodule.span ℝ ({x | ∃ i, x = F.p i} ∪ {x | ∃ i j, i ≠ j ∧ x ∈ Block F i j}) = ⊤ := by
  classical
  apply top_unique
  rw [← frameBlock_iSup_eq_top F]
  apply iSup_le
  intro s
  induction s using Sym2.ind with
  | _ i j =>
    rw [frameBlock_mk]
    by_cases h : i = j
    · subst j
      rw [frameBlockRaw_self_eq_span]
      apply Submodule.span_le.mpr
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)
    · intro x hx
      apply Submodule.subset_span
      right
      exact ⟨i, j, h, by simpa [Block, one_div] using (mem_frameBlockRaw_off h).mp hx⟩

/-- q_block: §2.1; F3. Q acts by the product of the two diagonal coefficients on a coherence block. -/
theorem q_block {n : ℕ} (F : JordanFrame J n) (lam : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) (x : J) (hx : x ∈ Block F i j) : Q (∑ k, lam k • F.p k) x = (lam i*lam j) • x := by
  classical
  have hi := hx.1
  have hj := hx.2
  have hz (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) : F.p k * x = 0 :=
    frame_mul_eq_zero_of_eigen_half F hij hki hkj (by simpa [one_div] using hi)
      (by simpa [one_div] using hj)
  let a : J := ∑ k, lam k • F.p k
  have ha : a * x = ((lam i + lam j) / 2) • x := by
    dsimp [a]
    rw [Finset.sum_mul]
    simp only [smul_mul_assoc]
    rw [← Finset.sum_subset (s₂ := Finset.univ) (s₁ := {i, j}) (by simp)
      (by intro k _ hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          simp [hz k hk.1 hk.2])]
    simp [hij, Ne.symm hij, hi, hj, smul_smul, ← add_smul]
    congr 1 <;> ring
  have hs : a * a = ∑ k, (lam k * lam k) • F.p k := by
    dsimp [a]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
    rw [Finset.sum_eq_single k]
    · simp [smul_mul_assoc, mul_smul_comm, F.orthIdem.idem k, smul_smul]
    · intro b hb hbk
      simp [smul_mul_assoc, mul_smul_comm, F.orthIdem.orth k b (Ne.symm hbk)]
    · simp
  have hsx : (a * a) * x = ((lam i * lam i + lam j * lam j) / 2) • x := by
    rw [hs, Finset.sum_mul]
    simp only [smul_mul_assoc]
    rw [← Finset.sum_subset (s₂ := Finset.univ) (s₁ := {i, j}) (by simp)
      (by intro k _ hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          simp [hz k hk.1 hk.2])]
    simp [hij, Ne.symm hij, hi, hj, smul_smul, ← add_smul]
    congr 1 <;> ring
  change (2 : ℝ) • (a * (a * x)) - (a * a) * x = _
  rw [ha, mul_smul_comm, ha, hsx, smul_smul, smul_smul, ← sub_smul]
  congr 1 <;> ring

/-- sqrt_spec: §2.1. The spectral positive square root squares to its input. -/
theorem sqrt_spec (a : J) (ha : Positive a) : Positive (sqrt a) ∧ sqrt a*sqrt a = a := by
  sorry

/-- sqrt_continuous: §2.1; prop:singular. Square root is continuous on the positive cone. -/
theorem sqrt_continuous : ContinuousOn (sqrt : J → J) {a | Positive a} := by
  sorry

/-- q_order_inverse: §2.1; F3. Quadratic square-root maps have positive quadratic inverse at strictly positive inputs. -/
theorem q_order_inverse (a : J) (ha : StrictPositive a) : (∀ x, Q (inverseSqrt a) (Q (sqrt a) x) = x) ∧ (∀ x, Q (sqrt a) (Q (inverseSqrt a) x) = x) ∧ (∀ x, Positive x → Positive (Q (sqrt a) x)) ∧ (∀ x, Positive x → Positive (Q (inverseSqrt a) x)) ∧ Q (sqrt a) 1 = a := by
  sorry

/-- q_covariance: §2.1; F3. Jordan automorphisms intertwine Q. -/
theorem q_covariance (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) (x y : J) : g (Q x y) = Q (g x) (g y) := by
  simp [Q, hg.2]

/-- order_auto_jordan: §2.1; F4. Unital linear square-cone order automorphisms preserve the Jordan product. -/
theorem order_auto_jordan (g : J ≃ₗ[ℝ] J) (hu : g 1 = 1) (ho : ∀ x, Positive (g x) ↔ Positive x) : JordanAuto g := by
  sorry

/-- order_norm_topology: S2 bridge. The order-unit norm gives the same sequential convergence as the supplied finite-dimensional norm. -/
theorem order_norm_topology (a : ℕ → J) (b : J) : Filter.Tendsto (fun n => ouNorm (a n-b)) Filter.atTop (nhds 0) ↔ Filter.Tendsto a Filter.atTop (nhds b) := by
  have hcomm (x y : J) : x * y = y * x := by
    first
    | exact mul_comm x y
    | exact?
  have haddL (x y z : J) : (x + y) * z = x * z + y * z := by
    first
    | exact add_mul x y z
    | exact?
    | rw [hcomm (x + y) z, hcomm x z, hcomm y z]
      exact?
  have haddR (x y z : J) : x * (y + z) = x * y + x * z := by
    rw [hcomm x (y + z), haddL, hcomm y x, hcomm z x]
  have hsmulL (r : ℝ) (x y : J) : (r • x) * y = r • (x * y) := by
    first
    | exact smul_mul_assoc r x y
    | exact?
  have hsmulR (r : ℝ) (x y : J) : x * (r • y) = r • (x * y) := by
    rw [hcomm x (r • y), hsmulL, hcomm y x]
  have hunitL (x : J) : (1 : J) * x = x := by
    first
    | exact one_mul x
    | exact?
    | rw [hcomm]
      exact?
  have hunitR (x : J) : x * (1 : J) = x := by
    rw [hcomm, hunitL]
  have hinner (x y z : J) :
      inner ℝ (x * y) z = inner ℝ x (y * z) := by
    first
    | exact?
    | rw [hcomm x y]
      exact?
    | cases ‹EuclideanJordanAlgebra J› <;> aesop
  let L : J → J →ₗ[ℝ] J := fun x =>
    { toFun := fun y => x * y
      map_add' := fun y z => haddR x y z
      map_smul' := by
        intro r y
        change x * (r • y) = r • (x * y)
        exact hsmulR r x y }
  let B₀ : J →ₗ[ℝ] (J →L[ℝ] J) :=
    { toFun := fun x => ⟨L x, (L x).continuous_of_finiteDimensional⟩
      map_add' := by
        intro x y
        ext z
        exact haddL x y z
      map_smul' := by
        intro r x
        ext y
        change (r • x) * y = r • (x * y)
        exact hsmulL r x y }
  let B : J →L[ℝ] (J →L[ℝ] J) :=
    ⟨B₀, B₀.continuous_of_finiteDimensional⟩
  have hB (x y : J) : B x y = x * y := rfl
  let e₀ : J ≃ₗ[ℝ] J :=
    { toFun := fun x => (2 : ℝ) • x
      invFun := fun x => (1 / 2 : ℝ) • x
      left_inv := by
        intro x
        norm_num [smul_smul]
      right_inv := by
        intro x
        norm_num [smul_smul]
      map_add' := by
        intro x y
        exact smul_add _ _ _
      map_smul' := by
        intro r x
        simp [smul_smul, mul_comm] }
  let e : J ≃L[ℝ] J :=
    { toLinearEquiv := e₀
      continuous_toFun := by
        change Continuous (fun x : J => (2 : ℝ) • x)
        exact continuous_const.smul continuous_id
      continuous_invFun := by
        change Continuous (fun x : J => (1 / 2 : ℝ) • x)
        exact continuous_const.smul continuous_id }
  have hBd : HasStrictFDerivAt (fun x : J => B x) B (1 : J) := by
    first
    | exact B.hasStrictFDerivAt
    | exact B.hasStrictFDerivAt (1 : J)
  have hsq : HasStrictFDerivAt (fun x : J => x * x)
      (e : J →L[ℝ] J) (1 : J) := by
    have hs := hBd.clm_apply (hasStrictFDerivAt_id (𝕜 := ℝ) (1 : J))
    have he :
        (B (1 : J)).comp (ContinuousLinearMap.id ℝ J) + B.flip (1 : J) =
          (e : J →L[ℝ] J) := by
      apply ContinuousLinearMap.ext
      intro x
      change (1 : J) * x + x * (1 : J) = (2 : ℝ) • x
      rw [hunitL, hunitR, two_smul]
    first
    | simpa only [he] using hs
    | convert hs using 1 <;>
        first
        | rfl
        | ext x
          simp [B, B₀, L, e, e₀, hunitL, hunitR, two_smul]
  have hmap :
      Filter.map (fun x : J => x * x) (nhds (1 : J)) =
        nhds ((1 : J) * 1) := by
    exact HasStrictFDerivAt.map_nhds_eq_of_equiv hsq
  have hrange : Set.range (fun x : J => x * x) ∈ nhds (1 : J) := by
    have h :
        Set.range (fun x : J => x * x) ∈
          Filter.map (fun x : J => x * x) (nhds (1 : J)) := by
      change ∀ᶠ x : J in nhds (1 : J), ∃ y : J, y * y = x * x
      exact Filter.Eventually.of_forall fun x => ⟨x, rfl⟩
    rw [hmap] at h
    simpa only [hunitL] using h
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hrange
  have hlocal (x : J) (hx : ‖x‖ < δ) : Positive (1 + x) := by
    apply hball
    change dist (1 + x) (1 : J) < δ
    simpa [dist_eq_norm] using hx
  have hscale (r : ℝ) (hr : 0 ≤ r) {x : J}
      (hx : Positive x) : Positive (r • x) := by
    obtain ⟨y, rfl⟩ := hx
    refine ⟨Real.sqrt r • y, ?_⟩
    simp only [hsmulL, hsmulR, smul_smul, Real.mul_self_sqrt hr]
  have hzero : Positive (0 : J) := ⟨0, (L 0).map_zero⟩
  let C : ℝ := 2 / δ
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (by norm_num) hδ
  have hfeas (x : J) :
      0 ≤ C * ‖x‖ ∧
        Below (-(C * ‖x‖) • (1 : J)) x ∧
        Below x ((C * ‖x‖) • (1 : J)) := by
    by_cases hx : x = 0
    · subst x
      simpa [Below] using
        (show 0 ≤ (0 : ℝ) ∧ Positive (0 : J) ∧ Positive (0 : J) from
          ⟨le_rfl, hzero, hzero⟩)
    let r : ℝ := C * ‖x‖
    have hr : 0 < r := mul_pos hC (norm_pos_iff.mpr hx)
    have hrne : r ≠ 0 := ne_of_gt hr
    have hlength : ‖r⁻¹ • x‖ = δ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      dsimp [r, C]
      field_simp [ne_of_gt hδ, norm_ne_zero_iff.mpr hx] <;> ring
    have hsmall : ‖r⁻¹ • x‖ < δ := by
      rw [hlength]
      linarith
    have hp := hscale r hr.le (hlocal (r⁻¹ • x) hsmall)
    have hm := hscale r hr.le
      (hlocal (-(r⁻¹ • x)) (by simpa only [norm_neg] using hsmall))
    change 0 ≤ r ∧ Below (-r • (1 : J)) x ∧ Below x (r • (1 : J))
    refine ⟨hr.le, ?_, ?_⟩
    · simpa [Below, smul_add, smul_smul, hrne, add_comm] using hp
    · simpa [Below, smul_add, smul_smul, hrne, sub_eq_add_neg] using hm
  have htrace (x : J) : inner ℝ (x * x) (1 : J) = ‖x‖ ^ 2 := by
    rw [hinner, hunitR]
    exact real_inner_self_eq_norm_sq x
  let M : ℝ := ‖B‖ + 1
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hBM : ‖B‖ ≤ M := by
    dsimp [M]
    linarith
  have hmul (x y : J) : ‖x * y‖ ≤ M * ‖x‖ * ‖y‖ := by
    calc
      ‖x * y‖ = ‖B x y‖ := rfl
      _ ≤ ‖B x‖ * ‖y‖ := (B x).le_opNorm y
      _ ≤ (‖B‖ * ‖x‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg y)
      _ ≤ M * ‖x‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBM (norm_nonneg x)) (norm_nonneg y)
  let K : ℝ := 2 * M * ‖(1 : J)‖ ^ 2 + ‖(1 : J)‖ + 1
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hbound (x : J) (r : ℝ) (hr : 0 ≤ r)
      (hp : Below (-r • (1 : J)) x) (hm : Below x (r • (1 : J))) :
      ‖x‖ ≤ K * r := by
    obtain ⟨u, hu⟩ := hp
    obtain ⟨v, hv⟩ := hm
    change u * u = x - (-r • (1 : J)) at hu
    change v * v = r • (1 : J) - x at hv
    have hsum : u * u + v * v = (2 * r) • (1 : J) := by
      calc
        u * u + v * v =
            (x + r • (1 : J)) + (r • (1 : J) - x) := by
          rw [hu, hv]
          simp only [neg_smul, sub_neg_eq_add]
        _ = r • (1 : J) + r • (1 : J) := by abel
        _ = (2 * r) • (1 : J) := by rw [two_mul, add_smul]
    have hsumtrace :
        ‖u‖ ^ 2 + ‖v‖ ^ 2 = (2 * r) * ‖(1 : J)‖ ^ 2 := by
      calc
        ‖u‖ ^ 2 + ‖v‖ ^ 2 = inner ℝ (u * u + v * v) (1 : J) := by
          rw [inner_add_left, htrace, htrace]
        _ = (2 * r) * ‖(1 : J)‖ ^ 2 := by
          rw [hsum, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hu2 : ‖u‖ ^ 2 ≤ (2 * r) * ‖(1 : J)‖ ^ 2 := by
      nlinarith [sq_nonneg ‖v‖]
    have hx : x = u * u - r • (1 : J) := by
      rw [hu]
      simp [neg_smul]
    calc
      ‖x‖ = ‖u * u - r • (1 : J)‖ := congrArg norm hx
      _ ≤ ‖u * u‖ + ‖r • (1 : J)‖ := norm_sub_le _ _
      _ = ‖u * u‖ + r * ‖(1 : J)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      _ ≤ M * ‖u‖ * ‖u‖ + r * ‖(1 : J)‖ :=
        add_le_add (hmul u u) le_rfl
      _ = M * ‖u‖ ^ 2 + r * ‖(1 : J)‖ := by ring
      _ ≤ M * ((2 * r) * ‖(1 : J)‖ ^ 2) + r * ‖(1 : J)‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hu2 hM.le) le_rfl
      _ = (2 * M * ‖(1 : J)‖ ^ 2 + ‖(1 : J)‖) * r := by ring
      _ ≤ K * r := by
        dsimp [K]
        nlinarith
  let S : J → Set ℝ := fun x =>
    {r | 0 ≤ r ∧ Below (-r • (1 : J)) x ∧ Below x (r • (1 : J))}
  have hSne (x : J) : (S x).Nonempty := ⟨C * ‖x‖, hfeas x⟩
  have hSbdd (x : J) : BddBelow (S x) :=
    ⟨0, fun _ hr => hr.1⟩
  have hnonneg (x : J) : 0 ≤ ouNorm x := by
    change 0 ≤ sInf (S x)
    exact le_csInf (hSne x) fun _ hr => hr.1
  have hupper (x : J) : ouNorm x ≤ C * ‖x‖ := by
    change sInf (S x) ≤ C * ‖x‖
    exact csInf_le (hSbdd x) (hfeas x)
  have hlower (x : J) : ‖x‖ ≤ K * ouNorm x := by
    have hl : ‖x‖ / K ≤ sInf (S x) := by
      apply le_csInf (hSne x)
      intro r hr
      apply (div_le_iff₀ hK).mpr
      simpa only [mul_comm] using hbound x r hr.1 hr.2.1 hr.2.2
    have hh := (div_le_iff₀ hK).mp hl
    change ‖x‖ ≤ K * sInf (S x)
    simpa only [mul_comm] using hh
  constructor
  · intro h
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg (a n - b)) (fun n => hlower (a n - b))
    simpa using h.const_mul K
  · intro h
    have hn := tendsto_iff_norm_sub_tendsto_zero.mp h
    apply squeeze_zero (fun n => hnonneg (a n - b)) (fun n => hupper (a n - b))
    simpa using hn.const_mul C

/-- span: lem:span. The effect interval contains its half-unit ball and spans J. -/
theorem span : (∀ x : J, ouNorm x ≤ 1/2 → IsEffect ((1/2 : ℝ) • (1 : J)+x)) ∧ Submodule.span ℝ {a : J | IsEffect a} = ⊤ := by
  have hcomm (x y : J) : x * y = y * x := by
    first
    | exact mul_comm x y
    | exact?
  have haddL (x y z : J) : (x + y) * z = x * z + y * z := by
    first
    | exact add_mul x y z
    | exact?
    | rw [hcomm (x + y) z, hcomm x z, hcomm y z]
      exact?
  have haddR (x y z : J) : x * (y + z) = x * y + x * z := by
    rw [hcomm x (y + z), haddL, hcomm y x, hcomm z x]
  have hsmulL (r : ℝ) (x y : J) : (r • x) * y = r • (x * y) := by
    first
    | exact smul_mul_assoc r x y
    | exact?
  have hsmulR (r : ℝ) (x y : J) : x * (r • y) = r • (x * y) := by
    rw [hcomm x (r • y), hsmulL, hcomm y x]
  have hunitL (x : J) : (1 : J) * x = x := by
    first
    | exact one_mul x
    | exact?
    | rw [hcomm]
      exact?
  have hunitR (x : J) : x * (1 : J) = x := by
    rw [hcomm, hunitL]
  have hinner (x y z : J) :
      inner ℝ (x * y) z = inner ℝ x (y * z) := by
    first
    | exact?
    | rw [hcomm x y]
      exact?
    | cases ‹EuclideanJordanAlgebra J› <;> aesop
  let L : J → J →ₗ[ℝ] J := fun x =>
    { toFun := fun y => x * y
      map_add' := fun y z => haddR x y z
      map_smul' := by
        intro r y
        change x * (r • y) = r • (x * y)
        exact hsmulR r x y }
  let B₀ : J →ₗ[ℝ] (J →L[ℝ] J) :=
    { toFun := fun x => ⟨L x, (L x).continuous_of_finiteDimensional⟩
      map_add' := by
        intro x y
        ext z
        exact haddL x y z
      map_smul' := by
        intro r x
        ext y
        change (r • x) * y = r • (x * y)
        exact hsmulL r x y }
  let B : J →L[ℝ] (J →L[ℝ] J) :=
    ⟨B₀, B₀.continuous_of_finiteDimensional⟩
  have hB (x y : J) : B x y = x * y := rfl
  let e₀ : J ≃ₗ[ℝ] J :=
    { toFun := fun x => (2 : ℝ) • x
      invFun := fun x => (1 / 2 : ℝ) • x
      left_inv := by
        intro x
        norm_num [smul_smul]
      right_inv := by
        intro x
        norm_num [smul_smul]
      map_add' := by
        intro x y
        exact smul_add _ _ _
      map_smul' := by
        intro r x
        simp [smul_smul, mul_comm] }
  let e : J ≃L[ℝ] J :=
    { toLinearEquiv := e₀
      continuous_toFun := by
        change Continuous (fun x : J => (2 : ℝ) • x)
        exact continuous_const.smul continuous_id
      continuous_invFun := by
        change Continuous (fun x : J => (1 / 2 : ℝ) • x)
        exact continuous_const.smul continuous_id }
  have hBd : HasStrictFDerivAt (fun x : J => B x) B (1 : J) := by
    first
    | exact B.hasStrictFDerivAt
    | exact B.hasStrictFDerivAt (1 : J)
  have hsq : HasStrictFDerivAt (fun x : J => x * x)
      (e : J →L[ℝ] J) (1 : J) := by
    have hs := hBd.clm_apply (hasStrictFDerivAt_id (𝕜 := ℝ) (1 : J))
    have he :
        (B (1 : J)).comp (ContinuousLinearMap.id ℝ J) + B.flip (1 : J) =
          (e : J →L[ℝ] J) := by
      apply ContinuousLinearMap.ext
      intro x
      change (1 : J) * x + x * (1 : J) = (2 : ℝ) • x
      rw [hunitL, hunitR, two_smul]
    first
    | simpa only [he] using hs
    | convert hs using 1 <;>
        first
        | rfl
        | ext x
          simp [B, B₀, L, e, e₀, hunitL, hunitR, two_smul]
  have hmap :
      Filter.map (fun x : J => x * x) (nhds (1 : J)) =
        nhds ((1 : J) * 1) := by
    exact HasStrictFDerivAt.map_nhds_eq_of_equiv hsq
  have hrange : Set.range (fun x : J => x * x) ∈ nhds (1 : J) := by
    have h :
        Set.range (fun x : J => x * x) ∈
          Filter.map (fun x : J => x * x) (nhds (1 : J)) := by
      change ∀ᶠ x : J in nhds (1 : J), ∃ y : J, y * y = x * x
      exact Filter.Eventually.of_forall fun x => ⟨x, rfl⟩
    rw [hmap] at h
    simpa only [hunitL] using h
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hrange
  have hlocal (x : J) (hx : ‖x‖ < δ) : Positive (1 + x) := by
    apply hball
    change dist (1 + x) (1 : J) < δ
    simpa [dist_eq_norm] using hx
  have hscale (r : ℝ) (hr : 0 ≤ r) {x : J}
      (hx : Positive x) : Positive (r • x) := by
    obtain ⟨y, rfl⟩ := hx
    refine ⟨Real.sqrt r • y, ?_⟩
    simp only [hsmulL, hsmulR, smul_smul, Real.mul_self_sqrt hr]
  have hzero : Positive (0 : J) := ⟨0, (L 0).map_zero⟩
  let C : ℝ := 2 / δ
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (by norm_num) hδ
  have hfeas (x : J) :
      0 ≤ C * ‖x‖ ∧
        Below (-(C * ‖x‖) • (1 : J)) x ∧
        Below x ((C * ‖x‖) • (1 : J)) := by
    by_cases hx : x = 0
    · subst x
      simpa [Below] using
        (show 0 ≤ (0 : ℝ) ∧ Positive (0 : J) ∧ Positive (0 : J) from
          ⟨le_rfl, hzero, hzero⟩)
    let r : ℝ := C * ‖x‖
    have hr : 0 < r := mul_pos hC (norm_pos_iff.mpr hx)
    have hrne : r ≠ 0 := ne_of_gt hr
    have hlength : ‖r⁻¹ • x‖ = δ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      dsimp [r, C]
      field_simp [ne_of_gt hδ, norm_ne_zero_iff.mpr hx] <;> ring
    have hsmall : ‖r⁻¹ • x‖ < δ := by
      rw [hlength]
      linarith
    have hp := hscale r hr.le (hlocal (r⁻¹ • x) hsmall)
    have hm := hscale r hr.le
      (hlocal (-(r⁻¹ • x)) (by simpa only [norm_neg] using hsmall))
    change 0 ≤ r ∧ Below (-r • (1 : J)) x ∧ Below x (r • (1 : J))
    refine ⟨hr.le, ?_, ?_⟩
    · simpa [Below, smul_add, smul_smul, hrne, add_comm] using hp
    · simpa [Below, smul_add, smul_smul, hrne, sub_eq_add_neg] using hm
  have hclosed : IsClosed {x : J | Positive x} := by
    have heq : {x : J | Positive x} = ⋂ b : J, ⋂ (_ : Positive b), {x : J | 0 ≤ inner ℝ x b} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact square_cone_selfdual x
    rw [heq]
    exact isClosed_iInter fun b => isClosed_iInter fun _ => isClosed_le continuous_const (continuous_id.inner continuous_const)
  let S : J → Set ℝ := fun x => {r | 0 ≤ r ∧ Below (-r • (1 : J)) x ∧ Below x (r • (1 : J))}
  have hSclosed (x : J) : IsClosed (S x) := by
    change IsClosed ({r : ℝ | 0 ≤ r} ∩ ({r : ℝ | Positive (x - (-r • (1 : J)))} ∩ {r : ℝ | Positive (r • (1 : J) - x)}))
    refine isClosed_Ici.inter (IsClosed.inter ?_ ?_)
    · exact hclosed.preimage (by fun_prop)
    · exact hclosed.preimage (by fun_prop)
  have hattain (x : J) : sInf (S x) ∈ S x :=
    (hSclosed x).csInf_mem ⟨C * ‖x‖, hfeas x⟩ ⟨0, fun _ h => h.1⟩
  constructor
  · intro x hx
    have hh := hattain x
    change 0 ≤ ouNorm x ∧ Below (-ouNorm x • (1 : J)) x ∧ Below x (ouNorm x • (1 : J)) at hh
    have hunit : Positive ((1 : J)) := ⟨1, hunitL 1⟩
    have hconeadd {a b : J} (ha : Positive a) (hb : Positive b) : Positive (a + b) := by
      apply (square_cone_selfdual _).mpr
      intro z hz
      rw [inner_add_left]
      exact add_nonneg ((square_cone_selfdual _).mp ha z hz) ((square_cone_selfdual _).mp hb z hz)
    have hd := hscale ((1/2 : ℝ) - ouNorm x) (by linarith) hunit
    constructor
    · have hp := hconeadd hh.2.1 hd
      have heq : x - (-ouNorm x • (1 : J)) + ((1/2 : ℝ) - ouNorm x) • (1 : J) = (1/2 : ℝ) • (1 : J) + x := by
        rw [sub_smul, neg_smul]
        abel
      rw [heq] at hp
      exact hp
    · have hp := hconeadd hh.2.2 hd
      change Positive (1 - ((1/2 : ℝ) • (1 : J) + x))
      have heq : ouNorm x • (1 : J) - x + ((1/2 : ℝ) - ouNorm x) • (1 : J) = 1 - ((1/2 : ℝ) • (1 : J) + x) := by
        rw [sub_smul]
        module
      rw [heq] at hp
      exact hp
  · letI := orderUnitSpaceOfBilinear (jmulₗ J) (jmulₗ_comm (J := J)) jmulₗ_jordan jmulₗ_formallyReal (1 : J) jmulₗ_one_mul
    have heffect (a : J) : OrderUnitSpace.IsEffect a ↔ IsEffect a := by
      rw [isEffect_ofBilinear]
      simp only [IsEffect, Below]
      have hc (x : J) : IsSoS (jmulₗ J) x ↔ Positive x := by
        rw [isSoS_iff_exists_sq (jmulₗ_comm (J := J)) jmulₗ_jordan jmulₗ_formallyReal jmulₗ_inner_assoc (1 : J) jmulₗ_one_mul]
        constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, hy.symm⟩
      rw [hc, hc]
    have hspan : Submodule.span ℝ {a : J | OrderUnitSpace.IsEffect a} = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨r, hr0, hr⟩ := OrderUnitSpace.archimedean x
      obtain ⟨s, hs0, hs⟩ := OrderUnitSpace.archimedean (-x)
      set c : ℝ := r + s + 1 with hc
      have hcpos : (0 : ℝ) < c := by positivity
      -- `x + s • OrderUnitSpace.ousUnit` is nonnegative
      have hxs_nonneg : (0 : J) ≤ x + s • OrderUnitSpace.ousUnit := by
        have h := OrderUnitSpace.add_le_add_left (-x) (s • OrderUnitSpace.ousUnit) hs x
        rwa [add_neg_cancel] at h
      -- and bounded by `c • OrderUnitSpace.ousUnit`
      have hxs_le : x + s • OrderUnitSpace.ousUnit ≤ c • (OrderUnitSpace.ousUnit : J) := by
        calc x + s • OrderUnitSpace.ousUnit ≤ r • OrderUnitSpace.ousUnit + s • OrderUnitSpace.ousUnit := OrderUnitSpace.add_le_add_right' hr _
          _ = (r + s) • (OrderUnitSpace.ousUnit : J) := (add_smul r s OrderUnitSpace.ousUnit).symm
          _ ≤ c • (OrderUnitSpace.ousUnit : J) :=
              OrderUnitSpace.smul_le_smul_of_le_of_nonneg (by rw [hc]; linarith) OrderUnitSpace.ousUnit_nonneg
      -- so its `c`-rescaling is an effect
      have hy : OrderUnitSpace.IsEffect (c⁻¹ • (x + s • OrderUnitSpace.ousUnit)) := by
        refine ⟨OrderUnitSpace.smul_nonneg' (le_of_lt (inv_pos.mpr hcpos)) hxs_nonneg, ?_⟩
        have h := OrderUnitSpace.smul_nonneg_mono c⁻¹ (le_of_lt (inv_pos.mpr hcpos)) hxs_le
        rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hcpos), one_smul] at h
      -- and `x` is a combination of it and the unit
      have hx : x = c • (c⁻¹ • (x + s • OrderUnitSpace.ousUnit)) - s • OrderUnitSpace.ousUnit := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hcpos), one_smul]
        abel
      rw [hx]
      exact Submodule.sub_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span hy))
        (Submodule.smul_mem _ _ (Submodule.subset_span OrderUnitSpace.isEffect_unit))
    convert hspan using 1
    congr 1
    ext a
    exact (heffect a).symm

/-- zero_unit: lem:homog(ii). Zero and unit laws and the output interval bound. -/
theorem zero_unit (P : SequentialProduct J) (a b : J) (ha : IsEffect a) (hb : IsEffect b) : P.sp a 0 = 0 ∧ P.sp 0 a = 0 ∧ P.sp a 1 = a ∧ Positive (P.sp a b) ∧ Below (P.sp a b) a := by
  have hsq : (1 : J) * 1 = 1 := by
    first
    | exact one_mul (1 : J)
    | exact mul_one (1 : J)
    | exact EuclideanJordanAlgebra.one_mul (1 : J)
    | exact EuclideanJordanAlgebra.mul_one (1 : J)
    | exact EuclideanJordanAlgebra.unit_mul (1 : J)
    | exact EuclideanJordanAlgebra.mul_unit (1 : J)
    | cases ‹EuclideanJordanAlgebra J› <;> aesop
  have hzero : IsEffect (0 : J) :=
    ⟨⟨0, by simp⟩, ⟨1, by simpa only [sub_zero] using hsq⟩⟩
  have hone : IsEffect (1 : J) :=
    ⟨⟨1, hsq⟩, ⟨0, by simp⟩⟩
  have hz : ∀ x : J, IsEffect x → P.sp x 0 = 0 := by
    intro x hx
    have h := P.S1 x 0 0 hx hzero hzero
      (by simpa only [zero_add] using hzero)
    simp only [zero_add] at h
    have hh : P.sp x 0 + P.sp x 0 = P.sp x 0 + 0 := by
      simpa only [add_zero] using h.symm
    exact add_left_cancel hh
  have hzleft : ∀ x : J, IsEffect x → P.sp 0 x = 0 := by
    intro x hx
    exact P.S4 x 0 hx hzero (hz x hx)
  have hcomm : Compatible P.sp a 0 := by
    change P.sp a 0 = P.sp 0 a
    rw [hz a ha, hzleft a ha]
  have hunitcomm : P.sp a 1 = P.sp 1 a := by
    simpa only [Compatible, sub_zero] using
      P.S6_compl a 0 ha hzero hcomm
  have hu : P.sp a 1 = a := hunitcomm.trans (P.S3 a ha)
  have hcompl : IsEffect (1 - b) := by
    refine ⟨hb.2, ?_⟩
    change Positive (1 - (1 - b))
    have he : (1 : J) - (1 - b) = b := by abel
    rw [he]
    exact hb.1
  have hsum : b + (1 - b) = (1 : J) := by abel
  have hsumEffect : IsEffect (b + (1 - b)) := by
    rw [hsum]
    exact hone
  have hadd := P.S1 a b (1 - b) ha hb hcompl hsumEffect
  rw [hsum, hu] at hadd
  refine ⟨hz a ha, hzleft a ha, hu, (P.closed a b ha hb).1, ?_⟩
  change Positive (a - P.sp a b)
  have hdiff : a - P.sp a b = P.sp a (1 - b) := by
    calc
      a - P.sp a b =
          (P.sp a b + P.sp a (1 - b)) - P.sp a b :=
        congrArg (fun x : J => x - P.sp a b) hadd
      _ = P.sp a (1 - b) := by abel
  rw [hdiff]
  exact (P.closed a (1 - b) ha hcompl).1

/-- monotone_right: lem:homog proof; S1 consequence. Right monotonicity is derived from S1 and closure. -/
theorem monotone_right (P : SequentialProduct J) (a b c : J) (ha : IsEffect a) (hb : IsEffect b) (hc : IsEffect c) (hbc : Below b c) : Below (P.sp a b) (P.sp a c) := by
  have haddpos (x y : J) (hx : Positive x) (hy : Positive y) : Positive (x + y) := by
    apply (square_cone_selfdual (x + y)).2
    intro z hz
    rw [inner_add_left]
    exact add_nonneg ((square_cone_selfdual x).1 hx z hz)
      ((square_cone_selfdual y).1 hy z hz)
  have hdiff : IsEffect (c - b) := by
    refine ⟨hbc, ?_⟩
    change Positive (1 - (c - b))
    have heq : (1 : J) - (c - b) = (1 - c) + b := by abel
    rw [heq]
    exact haddpos _ _ hc.2 hb.1
  have heq : b + (c - b) = c := by abel
  have hsum : IsEffect (b + (c - b)) := by rw [heq]; exact hc
  have h := P.S1 a b (c - b) ha hb hdiff hsum
  rw [heq] at h
  change Positive (P.sp a c - P.sp a b)
  rw [h]
  have heq' : P.sp a b + P.sp a (c - b) - P.sp a b = P.sp a (c - b) := by abel
  rw [heq']
  exact (P.closed a (c - b) ha hdiff).1

/-- linear_extension: lem:homog(i). Unique positive continuous linear extension of left multiplication. -/
theorem linear_extension (P : SequentialProduct J) (a : J) (ha : IsEffect a) : (∀ b, IsEffect b → leftMap P a b = P.sp a b) ∧ (∀ x, Positive x → Positive (leftMap P a x)) ∧ ∀ L : J →L[ℝ] J, (∀ b, IsEffect b → L b = P.sp a b) → L = leftMap P a :=
  leftMap_spec P a ha

/-- left_norm: lem:homog(iii). The order-unit operator norm equals the norm of a. -/
theorem left_norm (P : SequentialProduct J) (a : J) (ha : IsEffect a) : sSup {r : ℝ | ∃ x : J, ouNorm x ≤ 1 ∧ r = ouNorm (leftMap P a x)} = ouNorm a := by
  sorry

/-- scalars: lem:scalars. Scalar compatibility, scalar left maps, and first-slot homogeneity. -/
theorem scalars (P : SequentialProduct J) (a : J) (ha : IsEffect a) (q : ℝ) (hq : q ∈ Set.Icc 0 1) : Compatible P.sp a (q • (1 : J)) ∧ leftMap P (q • (1 : J)) = q • ContinuousLinearMap.id ℝ J ∧ leftMap P (q • a) = q • leftMap P a := by
  sorry

/-- continuity: lem:continuity. The left-map family is operator-norm continuous on effects. -/
theorem continuity (P : SequentialProduct J) : ContinuousOn (leftMap P) {a | IsEffect a} := by
  sorry

/-- orth_idem: lem:orth-idem. Orthogonal idempotent order intervals intersect only at zero. -/
theorem orth_idem (p q x : J) (hp : Idempotent p) (hq : Idempotent q) (hpq : p*q = 0) (hx : Positive x) (hxp : Below x p) (hxq : Below x q) : x = 0 := by
  have hc := EuclideanJordanAlgebra.mul_comm (J := J)
  have hu : ∀ z : J, (1 : J) * z = z := by
    intro z
    first
    | exact EuclideanJordanAlgebra.one_mul z
    | exact EuclideanJordanAlgebra.mul_one z
    | simpa only [hc] using EuclideanJordanAlgebra.one_mul z
    | simpa only [hc] using EuclideanJordanAlgebra.mul_one z
    | exact one_mul z
  have hur : ∀ z : J, z * 1 = z := by
    intro z
    rw [hc z 1, hu]
  have hj : ∀ u v : J, (u * u) * (v * u) = ((u * u) * v) * u := by
    intro u v
    calc
      (u * u) * (v * u) = (u * u) * (u * v) := by rw [hc v u]
      _ = u * ((u * u) * v) := (EuclideanJordanAlgebra.jordan u v).symm
      _ = ((u * u) * v) * u := hc u ((u * u) * v)
  have hs : ∀ e u v : J, inner ℝ (e * u) v = inner ℝ u (e * v) := by
    intro e u v
    exact EuclideanJordanAlgebra.inner_assoc e u v
  have hnonneg : ∀ e : J, Idempotent e →
      ∀ y : J, 0 ≤ inner ℝ (e * y) y := by
    intro e he y
    change e * e = e at he
    have hplus := hj (e + y) e
    have hminus := hj (e - y) e
    have heq := congrArg₂ (fun u v : J => u - v) hplus hminus
    have hy := hj y e
    simp only [mul_add, add_mul, mul_sub, sub_mul, he, hc] at heq
    have hpoly :
        (2 : ℝ) • (e * (e * (e * y))) -
          (3 : ℝ) • (e * (e * y)) + e * y = 0 := by
      simp only [hc] at heq hy ⊢
      linear_combination (norm := module) (-(1 / 2 : ℝ)) • heq + hy
    have h₁ := congrArg (fun z : J => inner ℝ z y) hpoly
    have h₂ := congrArg (fun z : J => inner ℝ z (e * y)) hpoly
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left,
      inner_zero_left] at h₁ h₂
    rw [hs e (e * (e * y)) y, hs e (e * y) y] at h₁
    rw [hs e (e * (e * y)) (e * y)] at h₂
    have hd : 0 ≤ inner ℝ (e * y - e * (e * y))
        (e * y - e * (e * y)) := by
      simpa using
        (show 0 ≤ RCLike.re (inner ℝ (e * y - e * (e * y))
          (e * y - e * (e * y))) from inner_self_nonneg)
    have hb : 0 ≤ inner ℝ (e * y) (e * y) := by
      simpa using
        (show 0 ≤ RCLike.re (inner ℝ (e * y) (e * y)) from inner_self_nonneg)
    simp only [inner_sub_left, inner_sub_right] at hd
    have hsym : inner ℝ (e * y) (e * (e * y)) =
        inner ℝ (e * (e * y)) (e * y) := real_inner_comm _ _
    rw [hsym] at hd
    nlinarith
  have hpair : ∀ e : J, Idempotent e →
      ∀ z : J, Positive z → 0 ≤ inner ℝ z e := by
    intro e he z hz
    rcases hz with ⟨y, rfl⟩
    have h := hnonneg e he y
    have hi : inner ℝ (y * y) e = inner ℝ (e * y) y := by
      rw [EuclideanJordanAlgebra.inner_assoc, hc y e, real_inner_comm]
    rw [hi]
    exact h
  have hq' : q * q = q := hq
  have hcomp : Idempotent (1 - q) := by
    change (1 - q) * (1 - q) = 1 - q
    simp only [sub_mul, mul_sub, hu, hur, hq']
    abel
  have hpqi : inner ℝ p q = 0 := by
    calc
      inner ℝ p q = inner ℝ (p * q) (1 : J) := by
        rw [EuclideanJordanAlgebra.inner_assoc, hur]
        exact (real_inner_comm p q).symm
      _ = 0 := by rw [hpq]; simp
  have hqci : inner ℝ q (1 - q) = 0 := by
    calc
      inner ℝ q (1 - q) = inner ℝ (q * (1 - q)) (1 : J) := by
        rw [EuclideanJordanAlgebra.inner_assoc, hur]
        exact (real_inner_comm q (1 - q)).symm
      _ = 0 := by simp only [mul_sub, hur, hq', sub_self, inner_zero_left]
  have h₁ := hpair q hq x hx
  have h₂ := hpair q hq (p - x) hxp
  rw [inner_sub_left, hpqi] at h₂
  have hxqi : inner ℝ x q = 0 := by linarith
  have h₃ := hpair (1 - q) hcomp x hx
  have h₄ := hpair (1 - q) hcomp (q - x) hxq
  rw [inner_sub_left, hqci] at h₄
  have hxci : inner ℝ x (1 - q) = 0 := by linarith
  apply (trace_faithful x hx).mp
  rw [inner_sub_right, hxqi, sub_zero] at hxci
  exact hxci

/-- frame_calculus: lem:frame-calculus. Effects diagonal in any COS are compatible and multiply spectrally. -/
theorem frame_calculus (P : SequentialProduct J) {n : ℕ} (F : COS J n) (lam μ : Fin n → ℝ) (hlam : ∀ i, lam i ∈ Set.Icc 0 1) (hμ : ∀ i, μ i ∈ Set.Icc 0 1) : let a := ∑ i, lam i • F.p i; let b := ∑ i, μ i • F.p i; Compatible P.sp a b ∧ P.sp a b = (∑ i, (lam i*μ i) • F.p i) ∧ P.sp a b = luders a b := by
  sorry

/-- positive_inverse: prop:theta proof. Invertible effects have positive inverse left maps via a scaled reciprocal effect. -/
theorem positive_inverse (P : SequentialProduct J) (a : J) (ha : IsEffect a) (hi : StrictPositive a) : ∃ b : J, IsEffect b ∧ ∃ μ : ℝ, 0 < μ ∧ (leftMap P a).comp (μ • leftMap P b) = ContinuousLinearMap.id ℝ J ∧ (μ • leftMap P b).comp (leftMap P a) = ContinuousLinearMap.id ℝ J := by
  sorry

/-- theta_auto: prop:theta. The comparison map is a Jordan automorphism and factors the product. -/
theorem theta_auto (P : SequentialProduct J) (a : J) (ha : IsEffect a) (hi : StrictPositive a) : ∃ g : J ≃ₗ[ℝ] J, JordanAuto g ∧ (∀ x, g x = theta P a x) ∧ ∀ b, IsEffect b → P.sp a b = Q (sqrt a) (g b) := by
  sorry

/-- theta_fix: prop:theta(i). Theta fixes every element in a COS diagonalizing a. -/
theorem theta_fix (P : SequentialProduct J) {n : ℕ} (F : COS J n) (a y : J) (ha : IsEffect a) (hi : StrictPositive a) (hfa : Diagonal F.p a) (hfy : Diagonal F.p y) : theta P a y = y := by
  sorry

/-- theta_continuous: prop:theta(ii). Theta is pointwise continuous on invertible effects. -/
theorem theta_continuous (P : SequentialProduct J) (x : J) : ContinuousOn (fun a => theta P a x) {a | IsEffect a ∧ StrictPositive a} := by
  sorry

/-- theta_cocycle: prop:theta(iii). Common-COS theta maps multiply and commute. -/
theorem theta_cocycle (P : SequentialProduct J) {n : ℕ} (F : COS J n) (a b x : J) (ha : IsEffect a) (hb : IsEffect b) (hia : StrictPositive a) (hib : StrictPositive b) (hfa : Diagonal F.p a) (hfb : Diagonal F.p b) : theta P (a*b) x = theta P a (theta P b x) ∧ theta P a (theta P b x) = theta P b (theta P a x) := by
  sorry

/-- coalescence: lem:coalescence. Theta is the identity on a corner where a is scalar. -/
theorem coalescence (P : SequentialProduct J) (q a₀ : J) (hq : Idempotent q) (h₀ : q*a₀ = 0) (lam : ℝ) (hlam : 0 < lam) (ha : IsEffect (lam • q+a₀)) (hi : StrictPositive (lam • q+a₀)) (y : J) (hy : q*y = y) : theta P (lam • q+a₀) y = y := by
  sorry

/-- frame_fix: lem:frame-fix. Theta fixes the frame, preserves each block, and admits a path to identity inside its stabilizer. -/
theorem frame_fix (P : SequentialProduct J) {n : ℕ} (F : JordanFrame J n) (r : Fin n → ℝ) (hr : ∀ i, r i ≤ 0) : (∀ i, theta P (twistElt F r) (F.p i) = F.p i) ∧ (∀ i j x, x ∈ Block F i j → theta P (twistElt F r) x ∈ Block F i j) ∧ ∃ γ : ℝ → J → J, (∀ x, ContinuousOn (fun s => γ s x) (Set.Icc 0 1)) ∧ (∀ x, γ 0 x = x ∧ γ 1 x = theta P (twistElt F r) x) ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ g : J ≃ₗ[ℝ] J, JordanAuto g ∧ (∀ x, g x = γ s x) ∧ ∀ i, g (F.p i) = F.p i := by
  sorry

/-- homomorphism: lem:homomorphism. Extend theta to a continuous exponential homomorphism with derivation differential and hyperplane factors. -/
theorem homomorphism (P : SequentialProduct J) {n : ℕ} (F : JordanFrame J n) : ∃ χ : (Fin n → ℝ) → (J →L[ℝ] J), ∃ D : (Fin n → ℝ) →L[ℝ] (J →L[ℝ] J), Continuous χ ∧ χ 0 = ContinuousLinearMap.id ℝ J ∧ (∀ r s, χ (r+s) = (χ r).comp (χ s)) ∧ (∀ r, (∀ i, r i ≤ 0) → ∀ x, χ r x = theta P (twistElt F r) x) ∧ HasFDerivAt χ D 0 ∧ (∀ r, χ r = NormedSpace.exp (D r)) ∧ (∀ r, Derivation (D r).toLinearMap) ∧ (∀ r i, D r (F.p i) = 0) ∧ ∃ T : Fin n → Fin n → (J →ₗ[ℝ] J), ∀ r i j x, i ≠ j → x ∈ Block F i j → D r x = (r i-r j) • T i j x := by
  sorry

/-- central_imaginary: prop:central-imaginary; algebraic kernel. Triple coupling forces all ordered-pair coordinate maps to multiplication by one commuting imaginary element. -/
theorem central_imaginary {K : Type} [NonUnitalNonAssocRing K] [Module ℝ K] [One K] (hleft : ∀ x : K, 1*x = x) (hright : ∀ x : K, x*1 = x) {n : ℕ} (hn : 3 ≤ n) (t : Fin n → Fin n → K →ₗ[ℝ] K) (re : K →ₗ[ℝ] ℝ) (htriple : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ x y, t i k (x*y) = t i j x*y ∧ t i k (x*y) = x*t j k y) (him : ∀ i j, i ≠ j → re (t i j 1) = 0) : ∃ γ : K, re γ = 0 ∧ (∀ x, γ*x = x*γ) ∧ ∀ i j, i ≠ j → ∀ x, t i j x = γ*x := by
  have third : ∀ i j : Fin n, ∃ k : Fin n, i ≠ k ∧ j ≠ k := by
    intro i j
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    let c : Fin n := ⟨2, by omega⟩
    by_cases hia : i = a <;> by_cases hja : j = a
    · exact ⟨b, by simp [hia, a, b], by simp [hja, a, b]⟩
    · by_cases hjb : j = b
      · exact ⟨c, by simp [hia, a, c], by simp [hjb, b, c]⟩
      · exact ⟨b, by simp [hia, a, b], hjb⟩
    · by_cases hib : i = b
      · exact ⟨c, by simp [hib, b, c], by simp [hja, a, c]⟩
      · exact ⟨b, hib, by simp [hja, a, b]⟩
    · exact ⟨a, hia, hja⟩
  have tri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      t i k 1 = t i j 1 ∧ t i k 1 = t j k 1 := by
    intro i j k hij hjk hik
    simpa only [hleft, hright] using htriple i j k hij hjk hik 1 1
  have source : ∀ i j k, i ≠ j → i ≠ k → t i j 1 = t i k 1 := by
    intro i j k hij hik
    by_cases hjk : j = k
    · subst k; rfl
    · exact (tri i j k hij hjk hik).1.symm
  have reverse : ∀ i j, i ≠ j → t i j 1 = t j i 1 := by
    intro i j hij
    obtain ⟨k, hik, hjk⟩ := third i j
    have h₁ := tri i j k hij hjk hik
    have h₂ := tri j i k hij.symm hik hjk
    exact h₁.1.symm.trans (h₁.2.trans h₂.1)
  have all_eq : ∀ i j k l, i ≠ j → k ≠ l → t i j 1 = t k l 1 := by
    intro i j k l hij hkl
    by_cases hik : i = k
    · subst k; exact source i j l hij hkl
    · calc
        t i j 1 = t i k 1 := source i j k hij hik
        _ = t k i 1 := reverse i k hik
        _ = t k l 1 := source k i l (Ne.symm hik) hkl
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  let γ := t a b 1
  have hγ : ∀ i j, i ≠ j → t i j 1 = γ := by
    intro i j hij
    exact all_eq i j a b hij hab
  refine ⟨γ, him a b hab, ?_, ?_⟩
  · intro x
    obtain ⟨k, hak, hbk⟩ := third a b
    have h := htriple a k b hak hbk.symm hab 1 x
    have h' := htriple a k b hak hbk.symm hab x 1
    simp only [hleft, hright] at h h'
    rw [hγ a k hak] at h
    rw [hγ k b hbk.symm] at h'
    exact h.1.symm.trans h'.2
  · intro i j hij x
    obtain ⟨k, hik, hjk⟩ := third i j
    have h := htriple i k j hik hjk.symm hij 1 x
    simp only [hleft] at h
    rw [hγ i k hik] at h
    exact h.1


/-- quaternion_center: §4.2. An imaginary quaternion commuting with every quaternion vanishes. -/
theorem quaternion_center (γ : Quaternion ℝ) (him : γ.re = 0) (hc : ∀ x, γ*x = x*γ) : γ = 0 := by
  let qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
  have hi := hc qi
  have hj := hc qj
  have himI : γ.imI = 0 := by
    have h := congrArg QuaternionAlgebra.imK hj
    simp only [Quaternion.imK_mul] at h
    simp [qj] at h
    nlinarith
  have himJ : γ.imJ = 0 := by
    have h := congrArg QuaternionAlgebra.imK hi
    simp only [Quaternion.imK_mul] at h
    simp [qi] at h
    nlinarith
  have himK : γ.imK = 0 := by
    have h := congrArg QuaternionAlgebra.imJ hi
    simp only [Quaternion.imJ_mul] at h
    simp [qi] at h
    nlinarith
  apply Quaternion.ext <;> assumption

/-- octonion_center: §4.2. An imaginary division octonion commuting with every octonion vanishes. -/
theorem octonion_center (γ : Oct) (him : γ.1.re = 0) (hc : ∀ x, octMul γ x = octMul x γ) : γ = 0 := by
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

/-- per_frame_rigid: prop:per-frame(i). Real, quaternionic and Albert models have identity theta on invertible diagonal effects. -/
theorem per_frame_rigid (P : SequentialProduct J) {n : ℕ} (F : JordanFrame J n) (hn : 3 ≤ n) (hmodel : Nonempty (RealModel J n) ∨ Nonempty (QuaternionModel J n) ∨ Nonempty (AlbertModel J)) (a : J) (ha : IsEffect a) (hi : StrictPositive a) (hd : Diagonal F.p a) : ∀ x, theta P a x = x := by
  sorry

/-- per_frame_complex: prop:per-frame(ii). A unique real twist parameter works throughout each complex frame. -/
theorem per_frame_complex (P : SequentialProduct J) {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n) (F : JordanFrame J n) : ∃! t : ℝ, FrameTwist M P F t := by
  sorry

/-- orientation: lem:orientation(i,ii). The cross-corner complex structure squares to minus identity and commutes with unitaries fixing both corners. -/
theorem orientation {n : ℕ} (q p : Matrix (Fin n) (Fin n) ℂ) (hq : q*q = q) (hp : p*p = p) (hqs : q.conjTranspose = q) (hps : p.conjTranspose = p) (hqp : q*p = 0) (x : Matrix (Fin n) (Fin n) ℂ) (hx : x ∈ CrossSpace q p) : CrossJ q p x ∈ CrossSpace q p ∧ CrossJ q p (CrossJ q p x) = -x ∧ ∀ u : Matrix (Fin n) (Fin n) ℂ, u*u.conjTranspose = 1 → u.conjTranspose*u = 1 → u*q*u.conjTranspose = q → u*p*u.conjTranspose = p → CrossJ q p (u*x*u.conjTranspose) = u*CrossJ q p x*u.conjTranspose := by
  classical
  rcases hx with ⟨hxs, hxdecomp⟩
  have hpq : p*q = 0 := by
    have h := congrArg Matrix.conjTranspose hqp
    simpa [Matrix.conjTranspose_mul, hqs, hps] using h
  have hstar : (q*x*p).conjTranspose = p*x*q := by
    simp [Matrix.conjTranspose_mul, hqs, hps, hxs, mul_assoc]
  have hj : CrossJ q p x = Complex.I • (q*x*p) - Complex.I • (p*x*q) := by
    rw [CrossJ, hstar]
  have hjs : (CrossJ q p x).conjTranspose = CrossJ q p x := by
    simp only [CrossJ, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose]
    simp
    module
  have hqa (y : Matrix (Fin n) (Fin n) ℂ) : q*(q*y*p)*p = q*y*p := by
    calc
      _ = (q*q)*y*(p*p) := by noncomm_ring
      _ = _ := by rw [hq, hp]
  have hqb (y : Matrix (Fin n) (Fin n) ℂ) : q*(p*y*q)*p = 0 := by
    calc
      _ = (q*p)*y*(q*p) := by noncomm_ring
      _ = 0 := by simp [hqp]
  have hpa (y : Matrix (Fin n) (Fin n) ℂ) : p*(q*y*p)*q = 0 := by
    calc
      _ = (p*q)*y*(p*q) := by noncomm_ring
      _ = 0 := by simp [hpq]
  have hpb (y : Matrix (Fin n) (Fin n) ℂ) : p*(p*y*q)*q = p*y*q := by
    calc
      _ = (p*p)*y*(q*q) := by noncomm_ring
      _ = _ := by rw [hp, hq]
  have hqj : q*CrossJ q p x*p = Complex.I • (q*x*p) := by
    simp only [hj, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      hqa, hqb, smul_zero, sub_zero]
  have hpj : p*CrossJ q p x*q = -Complex.I • (p*x*q) := by
    simp only [hj, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      hpa, hpb, smul_zero, zero_sub, neg_smul]
  refine ⟨⟨hjs, ?_⟩, ?_, ?_⟩
  · rw [hqj, hpj, hj]
    module
  · rw [CrossJ, hqj]
    simp only [Matrix.conjTranspose_smul, hstar, smul_smul]
    simp
    conv_rhs => rw [hxdecomp]
    module
  · intro u _huu huU huq hup
    have hcomm (a : Matrix (Fin n) (Fin n) ℂ) (ha : u*a*u.conjTranspose = a) :
        u*a = a*u := by
      calc
        u*a = u*a*(u.conjTranspose*u) := by rw [huU, mul_one]
        _ = (u*a*u.conjTranspose)*u := by noncomm_ring
        _ = a*u := by rw [ha]
    have hcommq := hcomm q huq
    have hcommp := hcomm p hup
    have hcommstar (a : Matrix (Fin n) (Fin n) ℂ)
        (has : a.conjTranspose = a) (ha : u*a = a*u) :
        a*u.conjTranspose = u.conjTranspose*a := by
      have h := congrArg Matrix.conjTranspose ha
      simpa [Matrix.conjTranspose_mul, has] using h
    have hstarp := hcommstar p hps hcommp
    have hcorner : q*(u*x*u.conjTranspose)*p = u*(q*x*p)*u.conjTranspose := by
      calc
        _ = (q*u)*x*(u.conjTranspose*p) := by noncomm_ring
        _ = (u*q)*x*(p*u.conjTranspose) := by rw [hcommq, hstarp]
        _ = _ := by noncomm_ring
    simp only [CrossJ, hcorner, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, mul_sub, sub_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    noncomm_ring

/-- adjacent: lem:adjacent. Adjacent complex frames have equal parameters. -/
theorem adjacent (P : SequentialProduct J) {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n) (F G : JordanFrame J n) (hFG : Adjacent F G) (s t : ℝ) (hs : FrameTwist M P F s) (ht : FrameTwist M P G t) : s = t := by
  sorry

/-- frame_connectivity: lem:frame-connectivity. Ordered complex frames are connected by finitely many two-atom moves. -/
theorem frame_connectivity {n : ℕ} (M : ComplexModel J n) (hn : 2 ≤ n) (F G : JordanFrame J n) : Relation.ReflTransGen (fun A B : JordanFrame J n => Adjacent A B) F G := by
  sorry

/-- singular_luders: prop:singular, first clause. Continuous agreement on invertible effects extends the Luders equality to all effects. -/
theorem singular_luders (P : SequentialProduct J) (h : ∀ a b, IsEffect a → StrictPositive a → IsEffect b → P.sp a b = luders a b) : Rigid P := by
  sorry

/-- singular_twist: prop:singular, second clause. A fixed complex twist on invertibles extends to singular effects. -/
theorem singular_twist (P : SequentialProduct J) {n : ℕ} (M : ComplexModel J n) (t : ℝ) (h : ∀ a b, IsEffect a → StrictPositive a → IsEffect b → M.map (P.sp a b) = twistFactor M t a*M.map b*(twistFactor M t a).conjTranspose) : Twist M t P.sp := by
  sorry

/-- complex_classification: thm:complex. Every complex product in rank at least three has exactly one global real twist. -/
theorem complex_classification (P : SequentialProduct J) {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n) : ∃! t : ℝ, Twist M t P.sp := by
  sorry

/-- twist_sufficiency: lem:twist-sufficiency. Every real t defines a full S1-S7 complex product, including at zero eigenvalues. -/
theorem twist_sufficiency {n : ℕ} (M : ComplexModel J n) (hn : 2 ≤ n) (t : ℝ) : ∃ P : SequentialProduct J, Twist M t P.sp := by
  sorry

/-- luders_sufficiency: omnibus converse; vdW A.6. The abstract EJA Luders product satisfies all seven clauses. -/
theorem luders_sufficiency : ∃ P : SequentialProduct J, Agrees P.sp luders := by
  sorry

/-- spin_geometry: §2.2. The spin cone is the cone of squares, and the order-unit norm is |alpha|+norm x. -/
theorem spin_geometry {d : ℕ} (hd : 2 ≤ d) (a : Spin d) : (spinPositive a ↔ ∃ x, spinMul x x = a) ∧ sInf {r : ℝ | 0 ≤ r ∧ spinPositive (r • spinUnit d+a) ∧ spinPositive (r • spinUnit d-a)} = |a.1|+‖a.2‖ := by
  constructor
  · constructor
    · intro ha
      rcases a with ⟨α, v⟩
      change ‖v‖ ≤ α at ha
      let p := Real.sqrt (α + ‖v‖)
      let q := Real.sqrt (α - ‖v‖)
      by_cases hv : v = 0
      · subst v
        refine ⟨(Real.sqrt α, 0), ?_⟩
        apply Prod.ext
        · dsimp [spinMul]
          have hα : 0 ≤ α := by simpa using ha
          have h := Real.sq_sqrt hα
          simp only [inner_zero_right, add_zero]
          nlinarith
        · simp [spinMul]
      · refine ⟨((p + q) / 2, ((p - q) / (2 * ‖v‖)) • v), ?_⟩
        apply Prod.ext
        · dsimp [spinMul]
          rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
          have hp := Real.sq_sqrt (show 0 ≤ α + ‖v‖ by linarith [norm_nonneg v])
          have hq := Real.sq_sqrt (show 0 ≤ α - ‖v‖ by linarith)
          have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
          dsimp [p, q] at *
          field_simp
          nlinarith [sq_nonneg (Real.sqrt (α + ‖v‖) - Real.sqrt (α - ‖v‖))]
        · dsimp [spinMul]
          simp only [smul_smul, ← add_smul]
          conv_rhs => rw [← one_smul ℝ v]
          congr 1
          have hp := Real.sq_sqrt (show 0 ≤ α + ‖v‖ by linarith [norm_nonneg v])
          have hq := Real.sq_sqrt (show 0 ≤ α - ‖v‖ by linarith)
          have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
          dsimp [p, q] at *
          field_simp
          nlinarith
    · rintro ⟨⟨t, v⟩, rfl⟩
      change ‖t • v + t • v‖ ≤ t * t + inner ℝ v v
      rw [← add_smul, norm_smul, Real.norm_eq_abs, real_inner_self_eq_norm_sq]
      have h := sq_nonneg (|t| - ‖v‖)
      have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
      have habs : |t + t| = 2 * |t| := by rw [← two_mul, abs_mul]; norm_num
      rw [habs]
      nlinarith [norm_nonneg v, abs_nonneg t]
  · let s : Set ℝ := {r : ℝ | 0 ≤ r ∧ spinPositive (r • (1, (0 : Vec d))+a) ∧ spinPositive (r • (1, (0 : Vec d))-a)}
    have hm : |a.1| + ‖a.2‖ ∈ s := by
      dsimp [s, spinPositive]
      simp only [Prod.smul_fst, Prod.smul_snd, smul_zero,
        Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, zero_add, zero_sub,
        norm_neg, smul_eq_mul, mul_one]
      constructor
      · positivity
      · constructor <;> linarith [le_abs_self a.1, neg_le_abs a.1]
    have hl : ∀ r ∈ s, |a.1| + ‖a.2‖ ≤ r := by
      intro r hr
      dsimp [s, spinPositive] at hr
      simp only [Prod.smul_fst, Prod.smul_snd, smul_zero,
        Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, zero_add, zero_sub,
        norm_neg, smul_eq_mul, mul_one] at hr
      rcases hr with ⟨_, hp, hm⟩
      have h : |a.1| ≤ r - ‖a.2‖ := (abs_le.mpr ⟨by linarith, by linarith⟩)
      linarith
    exact le_antisymm (csInf_le ⟨_, hl⟩ hm) (le_csInf ⟨_, hm⟩ hl)

/-- spin_automorphisms: §2.2. Spin-factor automorphisms act orthogonally on the vector part. -/
theorem spin_automorphisms {d : ℕ} (hd : 2 ≤ d) (g : Spin d ≃ₗ[ℝ] Spin d) (hu : g (spinUnit d) = spinUnit d) (hm : ∀ a b, g (spinMul a b) = spinMul (g a) (g b)) : ∃ O : Vec d ≃ₗᵢ[ℝ] Vec d, ∀ a, g a = (a.1, O a.2) := by
  have hscalar (t : ℝ) : g (t, 0) = (t, 0) := by
    have h := congrArg (fun x => t • x) hu
    simpa [spinUnit, ← map_smul] using h
  have hpure (v : Vec d) : (g (0, v)).1 = 0 := by
    have h := congrArg Prod.snd (hm (0, v) (0, v))
    simp only [spinMul, zero_mul, zero_add, zero_smul, add_zero, hscalar,
      Prod.snd] at h
    have hv : (g (0, v)).1 • (g (0, v)).2 = 0 := by
      have htwo : (2 : ℝ) • ((g (0, v)).1 • (g (0, v)).2) = 0 := by
        simpa [two_smul] using h.symm
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rcases smul_eq_zero.mp hv with h | h
    · exact h
    · have hg : g (0, v) = ((g (0, v)).1, 0) := by
        exact Prod.ext rfl h
      rw [← hscalar] at hg
      have he := g.injective hg
      exact (congrArg Prod.fst he).symm
  let f : Vec d →ₗ[ℝ] Vec d := {
    toFun := fun v => (g (0, v)).2
    map_add' := by
      intro x y
      simpa using congrArg Prod.snd (g.map_add (0, x) (0, y))
    map_smul' := by
      intro c x
      simpa using congrArg Prod.snd (g.map_smul c (0, x)) }
  have hnorm (v : Vec d) : ‖f v‖ = ‖v‖ := by
    have h := congrArg Prod.fst (hm (0, v) (0, v))
    simp only [spinMul, zero_mul, zero_add, zero_smul, add_zero, hscalar, Prod.fst, hpure] at h
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    dsimp [f]
    nlinarith [norm_nonneg v, norm_nonneg (g (0, v)).2]
  have hinj : Function.Injective f := by
    intro x y hxy
    have he : g (0, x) = g (0, y) := by
      apply Prod.ext
      · rw [hpure, hpure]
      · exact hxy
    exact congrArg Prod.snd (g.injective he)
  let O : Vec d ≃ₗᵢ[ℝ] Vec d := {
    toLinearEquiv := LinearEquiv.ofInjectiveEndo f hinj
    norm_map' := hnorm }
  refine ⟨O, ?_⟩
  intro a
  have ha : a = (a.1, 0) + (0, a.2) := by cases a; simp
  rw [ha, map_add, hscalar]
  apply Prod.ext
  · simp [hpure]
  · simp only [Prod.snd_add, zero_add]
    change (g (0, a.2)).2 = f a.2
    rfl

/-- spin_generator_continuous: §5.1 Steps 1-4. A continuous S1-S7 spin product determines a continuous odd skew axis field. -/
theorem spin_generator_continuous (P : SequentialProduct J) {d : ℕ} (M : SpinModel J d) (hd : 2 ≤ d) : ∃ A : AxisField d, ∀ a b, IsEffect a → StrictPositive a → IsEffect b → P.sp a b = spinOn M A a b := by
  sorry

/-- spin_sufficiency: §5.2. Every continuous odd axis field defines a full sequential product. -/
theorem spin_sufficiency {d : ℕ} (M : SpinModel J d) (hd : 2 ≤ d) (A : AxisField d) : ∃ P : SequentialProduct J, Agrees P.sp (spinOn M A) := by
  sorry

/-- spin_classification: thm:spin, bijection. Every spin product has exactly one field on the sphere; equality ignores arbitrary off-sphere extensions. -/
theorem spin_classification (P : SequentialProduct J) {d : ℕ} (M : SpinModel J d) (hd : 2 ≤ d) : ∃ A : AxisField d, Agrees P.sp (spinOn M A) ∧ ∀ B : AxisField d, Agrees P.sp (spinOn M B) → FieldEq B A := by
  sorry

/-- spin_compatibility: thm:spin, compatibility. Nonscalar spin effects are compatible exactly when their axes are collinear. -/
theorem spin_compatibility {d : ℕ} (hd : 2 ≤ d) (A : AxisField d) (a b : Spin d) (ha : spinEffect a) (hb : spinEffect b) (hna : a.2 ≠ 0) (hnb : b.2 ≠ 0) : spinProduct A a b = spinProduct A b a ↔ ∃ r : ℝ, a.2 = r • b.2 := by
  constructor
  · exact SpinCompatibility.compatible_implies_collinear A a b hb hna hnb
  · exact SpinCompatibility.collinear_implies_compatible A a b hna hnb

/-- real_qubit: cor:qubit-classification(i). A skew axis-fixing field in dimension two vanishes on the sphere. -/
theorem real_qubit (A : AxisField 2) : ∀ v, ‖v‖ = 1 → A.A v = 0 := by
  intro v hv
  let e₀ : Vec 2 := EuclideanSpace.single 0 1
  let e₁ : Vec 2 := EuclideanSpace.single 1 1
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hvcoord : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv0
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [h.1, h.2]
  have hdecomp : v = v 0 • e₀ + v 1 • e₁ := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [e₀, e₁]
  have h00 := A.skew v hv e₀ e₀
  have h11 := A.skew v hv e₁ e₁
  have h01 := A.skew v hv e₀ e₁
  simp [e₀, e₁, PiLp.inner_apply] at h00 h11 h01
  have hf : A.A v (v 0 • e₀ + v 1 • e₁) = 0 := by
    rw [← hdecomp]
    exact A.fixes v hv
  rw [map_add, map_smul, map_smul] at hf
  have hf0 := congrArg (fun x : Vec 2 => x 0) hf
  have hf1 := congrArg (fun x : Vec 2 => x 1) hf
  simp [e₀, e₁] at hf0 hf1
  have hd0 : (A.A v e₀) 0 = 0 := by dsimp [e₀] at *; linarith
  have hd1 : (A.A v e₁) 1 = 0 := by dsimp [e₁] at *; linarith
  have ha : (A.A v e₁) 0 = -(A.A v e₀) 1 := by
    simpa [e₀, e₁] using h01
  have hcoeff : (A.A v e₀) 1 = 0 := by
    have hp0 : v 0 * (A.A v e₀) 1 = 0 := by
      simpa [e₀, e₁, hd1] using hf1
    have hp1 : v 1 * (A.A v e₀) 1 = 0 := by
      have h : v 1 * (-(A.A v e₀) 1) = 0 := by
        simpa [e₀, e₁, hd0, ha] using hf0
      linarith
    rcases hvcoord with h | h
    · exact (mul_eq_zero.mp hp0).resolve_left h
    · exact (mul_eq_zero.mp hp1).resolve_left h
  have hz0 : A.A v e₀ = 0 := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [e₀, e₁] at * <;> linarith
  have hz1 : A.A v e₁ = 0 := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [e₀, e₁] at * <;> linarith
  apply ContinuousLinearMap.ext
  intro x
  have hx : x = x 0 • e₀ + x 1 • e₁ := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [e₀, e₁]
  rw [hx, map_add, map_smul, map_smul, hz0, hz1]
  simp

/-- qubit_field: cor:qubit-classification(ii), RP2 correspondence. Every three-dimensional axis field is exactly minus a continuous frame function times cross product. -/
theorem qubit_field (A : AxisField 3) : ∃! t : C(RP2, ℝ), FrameFunctionSpec t A := by
  exact QubitField.classification A

/-- qubit_classification: cor:qubit-classification(ii), product bijection. Complex-qubit spin products are parametrized by continuous functions on RP2. -/
theorem qubit_classification (P : SequentialProduct J) (M : SpinModel J 3) : ∃! t : C(RP2, ℝ), Agrees P.sp (spinOn M (fieldOfFrameFunction t)) := by
  sorry

/-- frame_dependent: ex:frame-dependent. The even squared-axis function takes both zero and one and is nonconstant. -/
theorem frame_dependent (ρ : Vec 3) (hρ : ‖ρ‖ = 1) : ∃ u v : sphere 3, (inner ℝ u.val ρ)^2 = 0 ∧ (inner ℝ v.val ρ)^2 = 1 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    simp [h] at hρ
  haveI : Fact (Module.finrank ℝ (Vec 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hd : Module.finrank ℝ (ℝ ∙ ρ)ᗮ = 2 := by
    exact Submodule.finrank_orthogonal_span_singleton (n := 2) hρ0
  have hn : (ℝ ∙ ρ)ᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hd
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have hi : inner ℝ w ρ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp hw
  refine ⟨⟨‖w‖⁻¹ • w, ?_⟩, ⟨ρ, hρ⟩, ?_, ?_⟩
  · exact norm_smul_inv_norm hw0
  · simp [real_inner_smul_left, hi]
  · rw [real_inner_self_eq_norm_sq, hρ]
    norm_num

/-- higher_spin_nonzero: rem:higher-spin, existence. Nonzero odd axis fields exist in every dimension at least three. -/
theorem higher_spin_nonzero (d : ℕ) (hd : 3 ≤ d) : ∃ A : AxisField d, ∃ v, ‖v‖ = 1 ∧ A.A v ≠ 0 := by
  exact higherSpinNonzero d hd

/-- higher_spin_covariance: rem:higher-spin, covariance. Rotation-covariant axis fields vanish for d at least four. -/
theorem higher_spin_covariance (d : ℕ) (hd : 4 ≤ d) (A : AxisField d) (hcov : ∀ O : Vec d ≃ₗᵢ[ℝ] Vec d, LinearMap.det O.toLinearEquiv.toLinearMap = 1 → ∀ v, ‖v‖ = 1 → ∀ w, A.A (O v) (O w) = O (A.A v w)) : ∀ v, ‖v‖ = 1 → A.A v = 0 := by
  intro v hv
  apply skew_covariant_zero hd (A.A v) v (A.fixes v hv) (A.skew v hv)
  intro O hdet hOv w
  have h := hcov O hdet v hv w
  simpa only [hOv] using h

/-- rigid: thm:rigid. Real rank two and up, quaternionic rank three and up, and Albert products are Luders on all effects. -/
theorem rigid (P : SequentialProduct J) (h : (∃ n, 2 ≤ n ∧ Nonempty (RealModel J n)) ∨ (∃ n, 3 ≤ n ∧ Nonempty (QuaternionModel J n)) ∨ Nonempty (AlbertModel J)) : Rigid P := by
  sorry

/-- rank_one: omnibus proof, rank-one case. The one-dimensional real product is forced to be multiplication. -/
theorem rank_one (P : SequentialProduct J) (M : RealModel J 1) : Rigid P := by
  sorry

/-- jvnw: §2.1; F6. Every simple EJA has one of the labelled coordinate models. -/
theorem jvnw (hJ : Simple J) : ∃ ℓ : Label, Realizes J ℓ := by
  sorry

/-- simple_decomposition: §2.1; omnibus input. Every finite-dimensional EJA is a finite direct sum of simple ideals. -/
theorem simple_decomposition : Nonempty (Decomposition J) := by
  exact Lib.simple_decomposition

/-- central: prop:central. Product restriction and assembly form an equivalence, with componentwise operational equality. -/
theorem central (D : Decomposition J) (P : ProductSpace J) (a b : Effects J) (i : Fin D.n) : D.equiv (P.val a b).val i = (((restrictProducts D P) i).val (componentEffect D a i) (componentEffect D b i)).val := by
  sorry

/-- master: mthm:master. Simple rank-at-least-three products are rigid outside the complex models, whose twist is unique. -/
theorem master (hJ : Simple J) (hrank : 3 ≤ EuclideanJordan.rank J) (P : SequentialProduct J) : (¬ HasComplexModel J → Rigid P) ∧ ∀ n (M : ComplexModel J n), 3 ≤ n → ∃! t : ℝ, Twist M t P.sp := by
  sorry

/-- simple_parametrization: mthm:omnibus simple-block step. For fixed coordinate identifications the parameter space exactly represents effect-level products. -/
theorem simple_parametrization (ℓ : Label) (M : ModelWitness J ℓ) : ∃ e : ProductSpace J ≃ ℓ.Param, ∀ P, ParamSpec ℓ M (e P) P := by
  sorry

/-- omnibus: mthm:omnibus. For fixed simple-summand identifications there is a bijection to independent complex and spin parameters. -/
theorem omnibus (D : Decomposition J) (ℓ : Fin D.n → Label) (M : ∀ i, ModelWitness (D.blocks i).V (ℓ i)) : ∃ e : ProductSpace J ≃ (∀ i, (ℓ i).Param), ∀ P i, ParamSpec (ℓ i) (M i) (e P i) ((restrictProducts D P) i) := by
  sorry

/-- dyn_equivalence: mthm:dyn(i). In simple rank at least three, a non-Luders product exists iff a dynamical correspondence exists iff a complex matrix model exists. -/
theorem dyn_equivalence (hJ : Simple J) (hrank : 3 ≤ EuclideanJordan.rank J) : ((∃ P : SequentialProduct J, ¬ Rigid P) ↔ Nonempty (DynamicalCorrespondence J)) ∧ (Nonempty (DynamicalCorrespondence J) ↔ HasComplexModel J) := by
  sorry

/-- dyn_form: mthm:dyn(ii). The twist is Q-sqrt followed by exp of twice t times the log-generated dynamical derivation. -/
theorem dyn_form {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n) (ψ : DynamicalCorrespondence J) (hψ : ∀ h x, M.map (ψ.psi h x) = (Complex.I/2) • (M.map h*M.map x-M.map x*M.map h)) (P : SequentialProduct J) (t : ℝ) (ht : Twist M t P.sp) (a b : J) (ha : IsEffect a) (hi : StrictPositive a) (hb : IsEffect b) (D : J →L[ℝ] J) (hD : ∀ x, D x = ψ.psi (log a) x) : P.sp a b = Q (sqrt a) (NormedSpace.exp ((2*t) • D) b) := by
  sorry

/-- dyn_rank_two: rem:dyn-rank-two. Spin factors other than d=3 have no dynamical correspondence, while d at least four admits non-Luders products. -/
theorem dyn_rank_two {d : ℕ} (M : SpinModel J d) (hd : 2 ≤ d) (hne : d ≠ 3) : ¬ Nonempty (DynamicalCorrespondence J) ∧ (4 ≤ d → ∃ P : SequentialProduct J, ¬ Rigid P) := by
  sorry

/-- sharp: cor:sharp. Every product is Luders on every sharp first effect. -/
theorem sharp (P : SequentialProduct J) (p b : J) (hp : Idempotent p) (hb : IsEffect b) : P.sp p b = Q p b := by
  sorry

/-- twist_detection: rem:twist-detection, displayed formula. The explicit two-by-two trace equals the proposed detection probability. -/
theorem twist_detection (t r φ : ℝ) (hr : 0 < r) : (Matrix.trace (detectionRho φ * (detectionFactor t r*detectionB*(detectionFactor t r).conjTranspose))).re = detection t r φ := by
  simp [detectionRho, detectionFactor, detectionB, detection, Matrix.trace,
    Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  rw [Real.cos_sub]
  have htrig := Real.cos_sq_add_sin_sq (t*r)
  have hexp : Real.exp (-(r / 2)) * Real.exp (-(r / 2)) = Real.exp (-r) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  have hscaled := congrArg (fun x : ℝ => Real.exp (-(r / 2)) ^ 2 * x) htrig
  have hn : -r / 2 = -(r / 2) := by ring
  rw [hn]
  nlinarith [hscaled]

/-- noiseless_identifiability: rem:twist-detection, two strengths. Two positive irrationally related strengths identify t in the noiseless model. -/
theorem noiseless_identifiability (t s r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hirr : ¬ ∃ q : ℚ, r₁/r₂ = (q : ℝ)) (h : ∀ φ, detection t r₁ φ = detection s r₁ φ ∧ detection t r₂ φ = detection s r₂ φ) : t = s := by
  have hs (r : ℝ) (hr : 0 < r)
      (h0 : detection t r 0 = detection s r 0)
      (h90 : detection t r (Real.pi/2) = detection s r (Real.pi/2)) :
      ∃ k : ℤ, t-s = (k : ℝ) * (2*Real.pi/r) := by
    have ha : Real.exp (-r/2)/2 ≠ 0 := ne_of_gt (by positivity)
    have hc : Real.cos (t*r) = Real.cos (s*r) := by
      simp only [detection, zero_sub, Real.cos_neg] at h0
      exact (mul_left_cancel₀ ha) (add_left_cancel h0)
    have hsin : Real.sin (t*r) = Real.sin (s*r) := by
      simp only [detection, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two,
        zero_mul, one_mul, zero_add] at h90
      exact (mul_left_cancel₀ ha) (add_left_cancel h90)
    have hcos : Real.cos (t*r - s*r) = 1 := by
      rw [Real.cos_sub, hc, hsin]
      nlinarith [Real.sin_sq_add_cos_sq (s*r)]
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).1 hcos
    refine ⟨k, ?_⟩
    apply (mul_right_cancel₀ (ne_of_gt hr))
    calc
      (t-s)*r = t*r-s*r := by ring
      _ = (k : ℝ)*(2*Real.pi) := hk.symm
      _ = ((k : ℝ)*(2*Real.pi/r))*r := by field_simp
  obtain ⟨k₁, hk₁⟩ := hs r₁ h₁ (h 0).1 (h (Real.pi/2)).1
  obtain ⟨k₂, hk₂⟩ := hs r₂ h₂ (h 0).2 (h (Real.pi/2)).2
  by_contra hne
  have hk₁0 : (k₁ : ℝ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hk₁
    exact hne (sub_eq_zero.mp hk₁)
  apply hirr
  refine ⟨(k₁ : ℚ) / (k₂ : ℚ), ?_⟩
  have hp : (2 : ℝ)*Real.pi ≠ 0 := by positivity
  have hr₁ : r₁ ≠ 0 := ne_of_gt h₁
  have hr₂ : r₂ ≠ 0 := ne_of_gt h₂
  have hk₂0 : (k₂ : ℝ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hk₂
    exact hne (sub_eq_zero.mp hk₂)
  push_cast
  field_simp
  have heq := hk₁.symm.trans hk₂
  field_simp at heq
  nlinarith

/-- moduli: rem:moduli, labelled bijection. The labelled complex product space is bijective to the real line. -/
theorem moduli {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n) : ∃ e : ProductSpace J ≃ ℝ, ∀ P, ParamSpec (.complex n hn) M (e P) P := by
  sorry

/-- selectors_trace: cor:selectors(ii). Trace-form self-adjointness selects Luders on complex rank at least three. -/
theorem selectors_trace {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n) (P : SequentialProduct J) (hs : ∀ a b c, IsEffect a → IsEffect b → IsEffect c → (Matrix.trace (M.map (P.sp a b)*M.map c)).re = (Matrix.trace (M.map b*M.map (P.sp a c))).re) : Rigid P := by
  sorry

/-- selectors_exchange: cor:selectors(i). Peirce exchange with the same complex orientation forces the twist parameter to zero. -/
theorem selectors_exchange (t : ℝ) (h : ∀ x y : ℝ, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 → Complex.exp (Complex.I*(t*Real.log (x/y))) = Complex.exp (Complex.I*(t*Real.log (y/x)))) : t = 0 := by
  open Filter in
  have he : ∀ r : ℝ, r < 0 → Complex.exp (Complex.I * ((t : ℂ) * r)) = Complex.exp (Complex.I * ((t : ℂ) * (-r))) := by
    intro r hr
    have hh := h (Real.exp r) 1 (Real.exp_pos r) (by simpa using (Real.exp_le_one_iff.mpr (le_of_lt hr))) (by norm_num) (by norm_num)
    simpa [Real.log_div, Real.log_exp, Real.exp_ne_zero, Complex.ofReal_neg] using hh
  have hev : (fun r : ℝ => Complex.exp (Complex.I * ((t : ℂ) * r))) =ᶠ[nhds (-1 : ℝ)] (fun r : ℝ => Complex.exp (Complex.I * ((t : ℂ) * (-r)))) := by
    filter_upwards [Iio_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with r hr
    exact he r hr
  have hof : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 (-1) := by
    simpa using! Complex.ofRealCLM.hasDerivAt (x := (-1 : ℝ))
  have hd1 := ((hof.const_mul (t : ℂ)).const_mul Complex.I).cexp
  have hd2 := (((hof.neg).const_mul (t : ℂ)).const_mul Complex.I).cexp
  have hh := hd1.unique (hd2.congr_of_eventuallyEq hev)
  have hz : (t : ℂ) = 0 := by
    have : Complex.exp (Complex.I * ((t : ℂ) * (-1 : ℝ))) * (Complex.I * (t : ℂ)) = 0 := by
      have : Complex.exp (Complex.I * ((t : ℂ) * (-1 : ℝ))) = Complex.exp (Complex.I * ((t : ℂ) * (-(-1 : ℝ)))) := he (-1) (by norm_num)
      simp only [Pi.neg_apply] at hh
      rw [← this] at hh
      simp only [mul_one, mul_neg] at hh
      linear_combination (1/2 : ℂ) * hh
    exact Or.resolve_left (mul_eq_zero.mp (Or.resolve_left (mul_eq_zero.mp this) (Complex.exp_ne_zero _))) Complex.I_ne_zero
  exact_mod_cast hz

/-- selectors_transpose: cor:selectors(iii); rem:moduli transpose action. Transpose covariance selects Luders. -/
theorem selectors_transpose {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n) (P : SequentialProduct J) (hs : ∀ a b aT bT, IsEffect a → IsEffect b → IsEffect aT → IsEffect bT → M.map aT = (M.map a).transpose → M.map bT = (M.map b).transpose → M.map (P.sp aT bT) = (M.map (P.sp a b)).transpose) : Rigid P := by
  sorry

/-- vdw_reconstruction: thm:vdw1. A finite-dimensional Archimedean order-unit space with the seven axioms is unitally order-isomorphic to an EJA. -/
theorem vdw_reconstruction {V : Type} [OrderUnitSpace V] [FiniteDimensional ℝ V] (harch : ∀ x : V, (∀ ε : ℝ, 0 < ε → -(ε • orderUnit V) ≤ x) → 0 ≤ x) (hnorm : ∀ x : V, ∀ r : ℝ, 0 ≤ r → (‖x‖ ≤ r ↔ -(r • orderUnit V) ≤ x ∧ x ≤ r • orderUnit V)) (P : OrderProduct V) : ∃ A : Object, ∃ e : V ≃ₗ[ℝ] A.V, e (orderUnit V) = 1 ∧ ∀ x, 0 ≤ x ↔ Positive (e x) := by
  sorry

/-- inverse_sqrt_continuous: prop:theta(ii) input. Inverse square root is continuous on the strictly positive cone. -/
theorem inverse_sqrt_continuous : ContinuousOn (inverseSqrt : J → J) {a | StrictPositive a} := by
  sorry

/-- q_diagonal: §2.1; F3. Q acts by the squared diagonal coefficient on each frame atom. -/
theorem q_diagonal {n : ℕ} (F : JordanFrame J n) (lam : Fin n → ℝ) (i : Fin n) : Q (∑ k, lam k • F.p k) (F.p i) = (lam i)^2 • F.p i := by
  classical
  have hp (i k : Fin n) : F.p k * F.p i = if k = i then F.p i else 0 := by
    split_ifs with h
    · subst k; exact F.orthIdem.idem i
    · exact F.orthIdem.orth k i h
  have hm (i : Fin n) : (∑ k, lam k • F.p k) * F.p i = lam i • F.p i := by
    rw [Finset.sum_mul]
    simp [smul_mul_assoc, hp]
  have hs : (∑ k, lam k • F.p k) * (∑ k, lam k • F.p k) =
      ∑ k, (lam k)^2 • F.p k := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_comm, mul_smul_comm, hm]
    simp [smul_smul, pow_two]
  have hm2 : (∑ k, (lam k)^2 • F.p k) * F.p i = (lam i)^2 • F.p i := by
    rw [Finset.sum_mul]
    simp [smul_mul_assoc, hp]
  rw [Q, hs, hm, mul_smul_comm, hm, hm2]
  simp only [smul_smul, ← sub_smul]
  congr 1 <;> ring

/-- q_cos_block: §2.1; F3, COS version. The quadratic multiplier formula also holds for a nonprimitive COS. -/
theorem q_cos_block {n : ℕ} (F : COS J n) (lam : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) (x : J) (hi : F.p i*x = (1/2 : ℝ) • x) (hj : F.p j*x = (1/2 : ℝ) • x) : Q (∑ k, lam k • F.p k) x = (lam i*lam j) • x := by
  classical
  have horth : IsOrthIdemFamily F.p := ⟨F.idem, F.orth⟩
  have hk (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) : F.p k * x = 0 := by
    have hq := add_idem_of_orthogonal (F.idem i) (F.idem j) (F.orth i j hij)
    have hqx : (F.p i + F.p j) * x = x := by
      rw [add_mul, hi, hj]
      module
    have hqk : (F.p i + F.p j) * F.p k = 0 := pair_mul_of_ne horth hki hkj
    have h := eigen_one_mul_zero hq hqx hqk
    simpa [mul_comm] using h
  have hlin (a : Fin n → ℝ) : (∑ k, a k • F.p k) * x =
      (a i / 2 + a j / 2) • x := by
    rw [Finset.sum_mul]
    have hterm (k : Fin n) : (a k • F.p k) * x =
        (if k = i then (a i / 2) • x else if k = j then (a j / 2) • x else 0) := by
      by_cases hki : k = i
      · subst k; simp [smul_mul_assoc, hi, smul_smul, div_eq_mul_inv]
      · by_cases hkj : k = j
        · subst k; simp [hki, smul_mul_assoc, hj, smul_smul, div_eq_mul_inv]
        · simp [hki, hkj, smul_mul_assoc, hk k hki hkj]
    simp_rw [hterm]
    simp only [show ∀ k : Fin n, (if k = i then (a i / 2) • x else if k = j then (a j / 2) • x else 0) = (if k = i then (a i / 2) • x else 0) + (if k = j then (a j / 2) • x else 0) by
      intro k; by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all]
    simp [Finset.sum_add_distrib, ← add_smul]
  have hs : (∑ k, lam k • F.p k) * (∑ k, lam k • F.p k) =
      ∑ k, (lam k)^2 • F.p k := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk'
    rw [mul_comm, mul_smul_comm, Finset.sum_mul]
    have hp (l : Fin n) : F.p l * F.p k = if l = k then F.p k else 0 := by
      split_ifs with h
      · subst l; exact F.idem k
      · exact F.orth l k h
    simp [smul_mul_assoc, hp, smul_smul, pow_two]
  rw [Q, hs, hlin, mul_smul_comm, hlin, hlin]
  simp only [smul_smul, ← sub_smul]
  congr 1 <;> ring

/-- jordan_transport: §4.3 proof; §2 transport. Unital Jordan identifications transport sequential products with S2. -/
theorem jordan_transport (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) (P : SequentialProduct J) : ∃ R : SequentialProduct J, ∀ a b, IsEffect a → IsEffect b → R.sp a b = g.symm (P.sp (g a) (g b)) := by
  exact exists_jordan_transport g hg P

/-- one_parameter_automatic: F5; §4.1, §5.1 Step 1. A continuous one-parameter group of finite-dimensional real operators is an exponential, without a differentiability premise. -/
theorem one_parameter_automatic (φ : ℝ → J →L[ℝ] J) (hc : Continuous φ) (h0 : φ 0 = ContinuousLinearMap.id ℝ J) (hm : ∀ s t, φ (s+t) = (φ s).comp (φ t)) : ∃! D : J →L[ℝ] J, ∀ t, φ t = NormedSpace.exp (t • D) := by
  open NormedSpace intervalIntegral MeasureTheory in
  have generic {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
      (g : ℝ → 𝔸) (hcont : Continuous g)
      (hmul : ∀ s t : ℝ, g (s + t) = g s * g t) (hone : g 0 = 1) :
      ∃! A : 𝔸, ∀ t : ℝ, g t = exp (t • A) := by
    have const_of_hasDerivAt_zero {φ : ℝ → 𝔸} (hφ : ∀ t, HasDerivAt φ 0 t) (t : ℝ) : φ t = φ 0 := by
      apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) (fun x => (hφ x).differentiableAt)
      intro x
      have h := (hφ x).hasFDerivAt.fderiv
      rw [h]
      exact ContinuousLinearMap.ext fun v => by simp
    classical
    -- ## Step 1: the regularizing integral and its inverse
    obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ s : ℝ, |s| < δ → ‖g s - 1‖ < 1 / 2 := by
      have h0 : ContinuousAt g 0 := hcont.continuousAt
      rw [Metric.continuousAt_iff] at h0
      obtain ⟨δ, hδpos, hδ⟩ := h0 (1 / 2) (by norm_num)
      refine ⟨δ, hδpos, fun s hs => ?_⟩
      have := hδ (x := s) (by simpa [Real.dist_eq] using hs)
      simpa [dist_eq_norm, hone] using this
    set d : ℝ := δ / 2 with hd
    have hdpos : 0 < d := by positivity
    have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) d, ‖g s - 1‖ ≤ 1 / 2 := by
      intro s hs
      rw [Set.uIoc_of_le (le_of_lt hdpos)] at hs
      have habs : |s| < δ := by
        rw [abs_lt]
        refine ⟨by linarith [hs.1], ?_⟩
        have h2 := hs.2
        rw [hd] at h2
        linarith
      exact le_of_lt (hδ s habs)
    set J : 𝔸 := ∫ s in (0 : ℝ)..d, g s with hJ
    have hJdev : ‖J - d • 1‖ ≤ d / 2 := by
      have hgi : IntervalIntegrable g volume 0 d := hcont.intervalIntegrable _ _
      have hsub : J - d • 1 = ∫ s in (0 : ℝ)..d, (g s - 1) := by
        rw [hJ, intervalIntegral.integral_sub hgi intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp
      rw [hsub]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := 1 / 2) (f := fun s => g s - 1) (a := (0 : ℝ)) (b := d) hbound
      calc ‖∫ s in (0:ℝ)..d, (g s - 1)‖ ≤ 1 / 2 * |d - 0| := h
        _ = d / 2 := by rw [sub_zero, abs_of_pos hdpos]; ring
    have htnorm : ‖(1 : 𝔸) - d⁻¹ • J‖ < 1 := by
      have h1 : (1 : 𝔸) - d⁻¹ • J = d⁻¹ • (d • 1 - J) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hdpos), one_smul]
      rw [h1, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hdpos]
      have h2 : ‖d • (1 : 𝔸) - J‖ ≤ d / 2 := by
        rw [← norm_neg]
        simpa using hJdev
      calc d⁻¹ * ‖d • (1:𝔸) - J‖ ≤ d⁻¹ * (d / 2) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 1 / 2 := by field_simp
        _ < 1 := by norm_num
    set u : 𝔸ˣ := Units.oneSub ((1 : 𝔸) - d⁻¹ • J) htnorm with hu
    have huval : (u : 𝔸) = d⁻¹ • J := by
      rw [hu, Units.val_oneSub, sub_sub_cancel]
    set Jinv : 𝔸 := d⁻¹ • (↑u⁻¹ : 𝔸) with hJinv
    have hJu : J = d • (u : 𝔸) := by
      rw [huval, smul_smul, mul_inv_cancel₀ (ne_of_gt hdpos), one_smul]
    have hJJinv : J * Jinv = 1 := by
      rw [hJu, hJinv, smul_mul_assoc, mul_smul_comm, smul_smul,
        mul_inv_cancel₀ (ne_of_gt hdpos), one_smul, u.mul_inv]
    -- ## Step 2: the translation identity and differentiability of g
    have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
      hcont.intervalIntegrable a b
    set F : ℝ → 𝔸 := fun t => ∫ s in (0 : ℝ)..t, g s with hF
    have htrans : ∀ t : ℝ, g t * J = F (t + d) - F t := by
      intro t
      have h1 : g t * J = ∫ s in (0 : ℝ)..d, g t * g s := by
        rw [hJ]
        exact ((ContinuousLinearMap.mul ℝ 𝔸 (g t)).intervalIntegral_comp_comm (hgi 0 d)).symm
      have h2 : (∫ s in (0 : ℝ)..d, g t * g s) = ∫ s in (0 : ℝ)..d, g (t + s) := by
        apply intervalIntegral.integral_congr
        intro s _
        exact (hmul t s).symm
      have h3 : (∫ s in (0 : ℝ)..d, g (t + s)) = ∫ s in t..(t + d), g s := by
        have := intervalIntegral.integral_comp_add_left (a := (0:ℝ)) (b := d) (f := g) t
        simpa using this
      have h4 : F t + ∫ s in t..(t + d), g s = F (t + d) :=
        intervalIntegral.integral_add_adjacent_intervals (hgi 0 t) (hgi t (t + d))
      rw [h1, h2, h3]
      exact eq_sub_of_add_eq' h4
    -- the primitive is differentiable with derivative g (FTC-2)
    have hFd : ∀ t : ℝ, HasDerivAt F (g t) t := by
      intro t
      exact intervalIntegral.integral_hasDerivAt_right (hgi 0 t)
        hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
    have hgrep : ∀ t : ℝ, g t = (F (t + d) - F t) * Jinv := by
      intro t
      calc g t = g t * 1 := (mul_one _).symm
        _ = g t * (J * Jinv) := by rw [hJJinv]
        _ = (g t * J) * Jinv := (mul_assoc _ _ _).symm
        _ = (F (t + d) - F t) * Jinv := by rw [htrans t]
    have hg' : ∀ t : ℝ, HasDerivAt g ((g (t + d) - g t) * Jinv) t := by
      intro t
      have hshift : HasDerivAt (fun t : ℝ => F (t + d)) (g (t + d)) t := by
        have hinner : HasDerivAt (fun t : ℝ => t + d) 1 t := (hasDerivAt_id t).add_const d
        have := (hFd (t + d)).scomp t hinner
        simpa using! this
      have hrepr : HasDerivAt (fun t => (F (t + d) - F t) * Jinv)
          ((g (t + d) - g t) * Jinv) t :=
        ((hshift.sub (hFd t)).mul_const Jinv)
      exact hrepr.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => (hgrep s))
    -- ## Step 3: the multiplicative derivative law
    have hA0' := hg' 0
    rw [zero_add, hone] at hA0'
    obtain ⟨A, hA0⟩ : ∃ A : 𝔸, HasDerivAt g A 0 := ⟨_, hA0'⟩
    have hmulderiv : ∀ t : ℝ, HasDerivAt g (g t * A) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => g t * g s) (g t * A) 0 := hA0.const_mul (g t)
      have h2 : (fun s : ℝ => g (t + s)) = fun s : ℝ => g t * g s :=
        funext fun s => hmul t s
      have h3 : HasDerivAt (fun s : ℝ => g (t + s)) (g t * A) 0 := h2 ▸ h1
      have h4 : HasDerivAt (fun s : ℝ => g (t + s)) ((g (t + d) - g t) * Jinv) 0 := by
        have hinner : HasDerivAt (fun s : ℝ => t + s) 1 0 := (hasDerivAt_id 0).const_add t
        have := (hg' (t + 0)).scomp 0 hinner
        simpa using! this
      have heq : (g (t + d) - g t) * Jinv = g t * A := h4.unique h3
      exact heq ▸ hg' t
    -- ## Step 4: the ODE kill
    have hAcomm : ∀ t : ℝ, A * exp (t • (-A)) = exp (t • (-A)) * A := by
      intro t
      have h1 : Commute A (t • (-A)) := ((Commute.refl A).neg_right).smul_right t
      exact (h1.exp_right).eq
    have hφ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => g t * exp (t • (-A))) 0 t := by
      intro t
      have hexp : HasDerivAt (fun t : ℝ => exp (t • (-A)))
          (exp (t • (-A)) * (-A)) t := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) t
      have h := (hmulderiv t).mul hexp
      have hzero : g t * A * exp (t • (-A)) + g t * (exp (t • (-A)) * (-A)) = 0 := by
        rw [mul_assoc, mul_neg, mul_neg, ← hAcomm t]
        exact add_neg_cancel _
      rw [hzero] at h
      exact h
    have hconst : ∀ t : ℝ, g t * exp (t • (-A)) = 1 := by
      intro t
      have h := const_of_hasDerivAt_zero hφ t
      simpa [hone] using h
    have hgA : ∀ t : ℝ, g t = exp (t • A) := by
      intro t
      have hEE : exp (t • (-A)) * exp (t • A) = 1 := by
        have hc : Commute (t • (-A)) (t • A) :=
          (((Commute.refl A).neg_left).smul_left t).smul_right t
        have hadd : exp ((t • (-A)) + t • A) = exp (t • (-A)) * exp (t • A) :=
          exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc
            ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
            ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
        rw [← hadd]
        simp
      calc g t = g t * 1 := (mul_one _).symm
        _ = g t * (exp (t • (-A)) * exp (t • A)) := by rw [hEE]
        _ = (g t * exp (t • (-A))) * exp (t • A) := (mul_assoc _ _ _).symm
        _ = exp (t • A) := by rw [hconst t, one_mul]
    -- ## Step 5: uniqueness
    refine ⟨A, hgA, ?_⟩
    intro B hB
    have hdB : HasDerivAt g B 0 := by
      have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) B 0
      have hfun : (fun u : ℝ => exp (u • B)) = g := (funext hB).symm
      rw [hfun] at h
      simpa using h
    exact hdB.unique hA0
  haveI : CompleteSpace J := FiniteDimensional.complete ℝ J
  exact generic φ hc (by simpa only [ContinuousLinearMap.mul_def] using hm) (by rw [ContinuousLinearMap.one_def]; exact h0)

/-- hyperplane_factor: lem:homomorphism last step. A linear operator-valued map vanishing on ri=rj factors through ri-rj. -/
theorem hyperplane_factor {n : ℕ} (i j : Fin n) (hij : i ≠ j) (D : (Fin n → ℝ) →ₗ[ℝ] (J →ₗ[ℝ] J)) (h : ∀ r, r i = r j → D r = 0) : ∃ T : J →ₗ[ℝ] J, ∀ r, D r = (r i-r j) • T := by
  let v : Fin n → ℝ := fun k => if k = i then 1 else 0
  refine ⟨D v, ?_⟩
  intro r
  let u : Fin n → ℝ := r - (r i - r j) • v
  have hs : u i = u j := by
    simp [u, v, Ne.symm hij] <;> ring
  have hz : D u = 0 := h u hs
  have heq : r = (r i - r j) • v + u := by
    dsimp [u]
    ext k
    by_cases hk : k = i <;> simp [v, hk] <;> ring
  calc
    D r = D ((r i - r j) • v + u) := congrArg D heq
    _ = (r i - r j) • D v := by
      rw [map_add, map_smul, hz]
      simp

/-- complex_imaginary: §4.2 centre computation. A purely imaginary complex number is uniquely i times a real number. -/
theorem complex_imaginary (γ : ℂ) (h : γ.re = 0) : ∃! t : ℝ, γ = Complex.I*t := by
  refine ⟨γ.im, ?_, ?_⟩
  · apply Complex.ext <;> simp [h]
  · intro t ht
    have him := congrArg Complex.im ht
    simpa using him.symm

/-- orientation_phase: lem:orientation(iii). Conjugation with phase lam on q and μ on p rotates the cross-corner by their phase difference. -/
theorem orientation_phase {n : ℕ} (q p u x : Matrix (Fin n) (Fin n) ℂ) (hq : q.conjTranspose = q) (hp : p.conjTranspose = p) (hx : x ∈ CrossSpace q p) (α β : ℝ) (huq : u*q = Complex.exp (Complex.I*α) • q) (hup : u*p = Complex.exp (Complex.I*β) • p) : u*x*u.conjTranspose = (Real.cos (α-β)) • x + (Real.sin (α-β)) • CrossJ q p x := by
  classical
  rcases hx with ⟨hxs, hxdecomp⟩
  have hstar : (q*x*p).conjTranspose = p*x*q := by
    simp [Matrix.conjTranspose_mul, hq, hp, hxs, mul_assoc]
  have hqu : q*u.conjTranspose = star (Complex.exp (Complex.I*α)) • q := by
    have h := congrArg Matrix.conjTranspose huq
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hq] using h
  have hpu : p*u.conjTranspose = star (Complex.exp (Complex.I*β)) • p := by
    have h := congrArg Matrix.conjTranspose hup
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hp] using h
  have hcorner (a b : Matrix (Fin n) (Fin n) ℂ) (lam mu : ℂ)
      (ha : u*a = lam • a) (hb : b*u.conjTranspose = mu • b) :
      u*(a*x*b)*u.conjTranspose = (lam*mu) • (a*x*b) := by
    calc
      _ = (u*a)*x*(b*u.conjTranspose) := by noncomm_ring
      _ = _ := by
        rw [ha, hb]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm lam mu]
  have hphase (a b : ℝ) :
      Complex.exp (Complex.I*a) * star (Complex.exp (Complex.I*b)) =
        (Real.cos (a-b) : ℂ) + (Real.sin (a-b) : ℂ)*Complex.I := by
    change Complex.exp (Complex.I*a) * starRingEnd ℂ (Complex.exp (Complex.I*b)) = _
    rw [← Complex.exp_conj, ← Complex.exp_add]
    have he : Complex.I*(a : ℂ) + starRingEnd ℂ (Complex.I*(b : ℂ)) =
        ((a-b : ℝ) : ℂ)*Complex.I := by
      simp
      ring
    rw [he, Complex.exp_ofReal_mul_I]
  have hab := hcorner q p _ _ huq hpu
  have hba := hcorner p q _ _ hup hqu
  rw [hphase] at hab hba
  have hcos : Real.cos (β-α) = Real.cos (α-β) := by
    rw [show β-α = -(α-β) by ring, Real.cos_neg]
  have hsin : Real.sin (β-α) = -Real.sin (α-β) := by
    rw [show β-α = -(α-β) by ring, Real.sin_neg]
  rw [hcos, hsin] at hba
  have hreal (r : ℝ) : r • x = r • (q*x*p + p*x*q) :=
    congrArg (fun y => r • y) hxdecomp
  calc
    u*x*u.conjTranspose = u*(q*x*p + p*x*q)*u.conjTranspose := by
      conv_lhs => rw [hxdecomp]
    _ = _ := by
      rw [mul_add, add_mul, hab, hba, hreal, CrossJ, hstar]
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul]
      ring

/-- strict_effect_density: prop:singular proof. Mixing an effect with the unit produces invertible effects and converges to the original effect. -/
theorem strict_effect_density (a : J) (ha : IsEffect a) : (∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsEffect ((1-ε) • a+ε • (1 : J)) ∧ StrictPositive ((1-ε) • a+ε • (1 : J))) ∧ Filter.Tendsto (fun ε : ℝ => (1-ε) • a+ε • (1 : J)) (nhds 0) (nhds a) := by
  exact strict_effect_density_aux a ha

/-- twist_scalar_zero: §2.1 zero convention; lem:twist-sufficiency. The scalar twist factor vanishes continuously at zero. -/
theorem twist_scalar_zero (t : ℝ) : ContinuousOn (fun x : ℝ => (Real.sqrt x : ℂ) * Complex.exp (Complex.I*(t*Real.log x))) (Set.Ici 0) ∧ (Real.sqrt 0 : ℂ) * Complex.exp (Complex.I*(t*Real.log 0)) = 0 := by
  open Filter in
  constructor
  · apply Continuous.continuousOn
    rw [continuous_iff_continuousAt]
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · unfold ContinuousAt
      simp only [Real.sqrt_zero, Complex.ofReal_zero, zero_mul]
      refine squeeze_zero_norm (fun x => ?_) (by simpa using Real.continuous_sqrt.tendsto 0)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x), ← Complex.ofReal_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    · exact (Complex.continuous_ofReal.continuousAt.comp Real.continuous_sqrt.continuousAt).mul
        (Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx)))))
  · simp

/-- twist_multiplicative: lem:twist-sufficiency proof. The scalar character has modulus square x and is multiplicative on nonnegative inputs. -/
theorem twist_multiplicative (t x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : Complex.normSq ((Real.sqrt x : ℂ)*Complex.exp (Complex.I*(t*Real.log x))) = x ∧ (Real.sqrt (x*y) : ℂ)*Complex.exp (Complex.I*(t*Real.log (x*y))) = ((Real.sqrt x : ℂ)*Complex.exp (Complex.I*(t*Real.log x)))*((Real.sqrt y : ℂ)*Complex.exp (Complex.I*(t*Real.log y))) := by
  constructor
  · rw [← Complex.sq_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x), ← Complex.ofReal_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Real.sq_sqrt hx]
  · rcases eq_or_lt_of_le hx with rfl | hx'
    · simp
    rcases eq_or_lt_of_le hy with rfl | hy'
    · simp
    rw [Real.sqrt_mul hx, Real.log_mul (ne_of_gt hx') (ne_of_gt hy')]
    push_cast
    rw [mul_add, mul_add, Complex.exp_add]
    ring

/-- spin_atoms: §2.2. Unit-vector spin atoms are idempotent and orthogonal to their antipodes. -/
theorem spin_atoms {d : ℕ} (v : Vec d) (hv : ‖v‖ = 1) : spinMul (spinAtom v) (spinAtom v) = spinAtom v ∧ spinMul (spinAtom v) (spinAtom (-v)) = 0 ∧ spinAtom v+spinAtom (-v) = spinUnit d := by
  have hi : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  simp only [spinMul, spinAtom, spinUnit, Prod.mk.injEq, Prod.fst_add, Prod.snd_add,
    Prod.fst_zero, Prod.snd_zero, real_inner_smul_left, real_inner_smul_right,
    inner_neg_right, hi]
  constructor
  · constructor
    · norm_num
    · module
  constructor
  · apply Prod.ext
    · norm_num
    · dsimp
      module
  · apply Prod.ext
    · norm_num
    · dsimp
      module

/-- spin_spectral: §2.2. Nonscalar spin elements have the stated axis and two eigenvalues. -/
theorem spin_spectral {d : ℕ} (a : Spin d) (hn : a.2 ≠ 0) : let v := ‖a.2‖⁻¹ • a.2; ‖v‖ = 1 ∧ a = (a.1+‖a.2‖) • spinAtom v + (a.1-‖a.2‖) • spinAtom (-v) := by
  rcases a with ⟨s, x⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hn
  have hvnorm : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    simp [hr.ne']
  have hvscale : ‖x‖ • (‖x‖⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  have hdecomp :
      (s + ‖x‖) • ((1 / 2 : ℝ) • (‖x‖⁻¹ • x)) +
        (s - ‖x‖) • ((1 / 2 : ℝ) • (-(‖x‖⁻¹ • x))) = x := by
    calc
      _ = ‖x‖ • (‖x‖⁻¹ • x) := by
        simp only [smul_neg, smul_smul]
        module
      _ = x := hvscale
  dsimp only
  constructor
  · exact hvnorm
  · apply Prod.ext
    · simp [spinAtom]
      ring
    · simpa [spinAtom, smul_neg, smul_smul] using hdecomp.symm

/-- spin_singular_formula: def:spin-product(iii). The singular branch is the rank-one Luders map. -/
theorem spin_singular_formula {d : ℕ} (A : AxisField d) (v : Vec d) (hv : ‖v‖ = 1) (lam : ℝ) (hlam : 0 < lam) (b : Spin d) : spinProduct A (lam • spinAtom v) b = (lam*(b.1+inner ℝ v b.2)) • spinAtom v := by
  have hp : 0 < lam / 2 := by positivity
  have hn : ‖(lam • spinAtom v).2‖ = lam / 2 := by
    simp [spinAtom, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, hv, abs_of_pos hp]
    ring
  have ha : (lam • spinAtom v).1 = lam / 2 := by simp [spinAtom]; ring
  have hx : (lam • spinAtom v).2 = (lam / 2) • v := by simp [spinAtom, smul_smul]; congr 1 <;> ring
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hx0 : (lam • spinAtom v).2 ≠ 0 := by rw [hx]; exact smul_ne_zero (ne_of_gt hp) hv0
  have hu : ‖(lam • spinAtom v).2‖⁻¹ • (lam • spinAtom v).2 = v := by
    rw [hn, hx, smul_smul, inv_mul_cancel₀ (ne_of_gt hp), one_smul]
  rw [hn] at hu
  rw [spinProduct, if_neg hx0]
  dsimp only
  rw [hn, ha, hu, hx]
  simp only [sub_self, Real.sqrt_zero, zero_smul, add_zero, spinAtom, Prod.smul_fst, Prod.smul_snd, inner_smul_left, real_inner_smul_left]
  apply Prod.ext
  · dsimp; simp only [starRingEnd_apply, star_trivial]; ring
  · dsimp; simp only [smul_smul]; module

/-- spin_field_bounded: §5.2 S2 input. Continuous fields on the sphere are uniformly bounded. -/
theorem spin_field_bounded {d : ℕ} (A : AxisField d) : ∃ M : ℝ, ∀ v, ‖v‖ = 1 → ‖A.A v‖ ≤ M := by
  let s : Set (Vec d) := {v | ‖v‖ = 1}
  let f : Vec d → ℝ := fun v => ‖A.A v‖
  have hs : IsCompact s := by
    simpa [s, Metric.sphere, dist_eq_norm] using
      (isCompact_sphere (0 : Vec d) 1)
  have hf : ContinuousOn f s := by
    simpa [f, s] using A.continuous.norm
  obtain ⟨M, hM⟩ := hs.bddAbove_image hf
  refine ⟨M, fun v hv => ?_⟩
  have hmem : f v ∈ f '' s := ⟨v, hv, rfl⟩
  exact hM hmem

/-- spin_generator_bound: §5.1 Step 3. Uniform continuity of skew exponential lines at zero bounds all their generators. -/
theorem spin_generator_bound {d : ℕ} (A : sphere d → (Vec d →L[ℝ] Vec d)) (hskew : ∀ v x y, inner ℝ x (A v y) = -inner ℝ (A v x) y) (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v t, |t| < δ → ‖NormedSpace.exp (t • A v)-ContinuousLinearMap.id ℝ (Vec d)‖ < ε) : ∃ M : ℝ, ∀ v, ‖A v‖ ≤ M := by
  exact uniform_exp_generator_bound A hsmall

/-- principal_skew_log: §5.1 Step 4. The exponential of skew operators of norm less than pi has a continuous inverse on its image. -/
theorem principal_skew_log (d : ℕ) : ∃ L : (Vec d →L[ℝ] Vec d) → (Vec d →L[ℝ] Vec d), ContinuousOn L {R | ∃ A : Vec d →L[ℝ] Vec d, (∀ x y, inner ℝ x (A y) = -inner ℝ (A x) y) ∧ ‖A‖ < Real.pi ∧ NormedSpace.exp A = R} ∧ ∀ A : Vec d →L[ℝ] Vec d, (∀ x y, inner ℝ x (A y) = -inner ℝ (A x) y) → ‖A‖ < Real.pi → L (NormedSpace.exp A) = A := by
  sorry

/-- spin_s2: §5.2 S2, all four strata. The spin product is continuous on effects, including scalar, singular and zero first effects. -/
theorem spin_s2 {d : ℕ} (A : AxisField d) (b : Spin d) (hb : spinEffect b) : ContinuousOn (fun a => spinProduct A a b) {a | spinEffect a} := by
  exact spin_s2_of_bounded A (spin_field_bounded A) (spin_singular_formula A) b

/-- spin_s4: §5.2 S4. Orthogonality of spin products is symmetric, singular cases included. -/
theorem spin_s4 {d : ℕ} (A : AxisField d) (a b : Spin d) (ha : spinEffect a) (hb : spinEffect b) (h : spinProduct A a b = 0) : spinProduct A b a = 0 := by
  sorry

/-- spin_s5: §5.2 S5. Compatible spin effects associate under the candidate product. -/
theorem spin_s5 {d : ℕ} (A : AxisField d) (a b c : Spin d) (ha : spinEffect a) (hb : spinEffect b) (hc : spinEffect c) (hab : spinProduct A a b = spinProduct A b a) : spinProduct A a (spinProduct A b c) = spinProduct A (spinProduct A a b) c := by
  sorry

/-- spin_transport: rem:higher-spin transport formula; ex:frame-dependent. Orthogonal transport conjugates the generator field and the spin product. -/
theorem spin_transport {d : ℕ} (A B : AxisField d) (O : Vec d ≃ₗᵢ[ℝ] Vec d) (h : ∀ v, ‖v‖ = 1 → ∀ w, B.A (O v) (O w) = O (A.A v w)) (a b : Spin d) (ha : spinEffect a) (hb : spinEffect b) : spinProduct B (a.1,O a.2) (b.1,O b.2) = ((spinProduct A a b).1, O (spinProduct A a b).2) := by
  exact spin_product_transport A B O h a b

/-- qubit_field_constructor: cor:qubit-classification(ii), constructive direction. The constructed RP2 field has the required signed cross-product formula. -/
theorem qubit_field_constructor (t : C(RP2, ℝ)) : FrameFunctionSpec t (fieldOfFrameFunction t) := by
  exact QubitField.constructor_spec t

/-- higher_spin_so3: rem:higher-spin d=3 covariance. SO(3) covariance makes the frame function constant. -/
theorem higher_spin_so3 (t : C(RP2, ℝ)) (h : ∀ O : Vec 3 ≃ₗᵢ[ℝ] Vec 3, LinearMap.det O.toLinearEquiv.toLinearMap = 1 → ∀ v : sphere 3, t (rp2Class ⟨O v.val, by simpa using v.property⟩) = t (rp2Class v)) : ∃ c : ℝ, ∀ x, t x = c := by
  exact QubitField.invariant_constant t h

/-- dynamical_matrix: §6.1 proof, commutator normalization. The matrix commutator with i/2 gives a dynamical correspondence. -/
theorem dynamical_matrix {n : ℕ} (M : ComplexModel J n) : ∃ ψ : DynamicalCorrespondence J, ∀ a b, M.map (ψ.psi a b) = (Complex.I/2) • (M.map a*M.map b-M.map b*M.map a) := by
  exact MatrixDynamics.exists_correspondence M

/-- twist_transpose: rem:moduli. Transpose transports t to minus t. -/
theorem twist_transpose {n : ℕ} (M : ComplexModel J n) (P R : SequentialProduct J) (t : ℝ) (ht : Twist M t P.sp) (hR : ∀ a b aT bT, IsEffect a → IsEffect b → IsEffect aT → IsEffect bT → M.map aT = (M.map a).transpose → M.map bT = (M.map b).transpose → M.map (R.sp aT bT) = (M.map (P.sp a b)).transpose) : Twist M (-t) R.sp := by
  sorry

/-- composition: rem:composition. Restriction from a standard complex tensor composite forces both factors to share its twist. -/
theorem composition {K L : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [EuclideanJordanAlgebra K] [FiniteDimensional ℝ K] [NormedAddCommGroup L] [InnerProductSpace ℝ L] [EuclideanJordanAlgebra L] [FiniteDimensional ℝ L] {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (MA : ComplexModel J n) (MB : ComplexModel K m) (MC : MatrixModel L ℂ (·*·) star 1 (n*m)) (PA : SequentialProduct J) (PB : SequentialProduct K) (PC : SequentialProduct L) (ιA : J →ₗ[ℝ] L) (ιB : K →ₗ[ℝ] L) (e : Fin (n*m) ≃ Fin n × Fin m) (hA : ∀ a i j, MC.map (ιA a) i j = MA.map a (e i).1 (e j).1 * (if (e i).2 = (e j).2 then 1 else 0)) (hB : ∀ b i j, MC.map (ιB b) i j = (if (e i).1 = (e j).1 then 1 else 0) * MB.map b (e i).2 (e j).2) (hrA : ∀ a b, IsEffect a → IsEffect b → PC.sp (ιA a) (ιA b) = ιA (PA.sp a b)) (hrB : ∀ a b, IsEffect a → IsEffect b → PC.sp (ιB a) (ιB b) = ιB (PB.sp a b)) : ∃ t : ℝ, Twist MC t PC.sp ∧ Twist MA t PA.sp ∧ Twist MB t PB.sp := by
  sorry

/-- twist_weak_selectors: §6.3 after selectors. Positive invertible effects stay invertible under every twist; this weaker condition cannot select zero. -/
theorem twist_weak_selectors {n : ℕ} (M : ComplexModel J n) (P : SequentialProduct J) (t : ℝ) (ht : Twist M t P.sp) (a b : J) (ha : IsEffect a) (hb : IsEffect b) (hia : StrictPositive a) (hib : StrictPositive b) : StrictPositive (P.sp a b) := by
  sorry

/-- effects_interior: lem:span, interior clause. The effect interval has nonempty interior. -/
theorem effects_interior : (interior {a : J | IsEffect a}).Nonempty := by
  have hcomm (x y : J) : x * y = y * x := by
    first
    | exact mul_comm x y
    | exact?
  have haddL (x y z : J) : (x + y) * z = x * z + y * z := by
    first
    | exact add_mul x y z
    | exact?
    | rw [hcomm (x + y) z, hcomm x z, hcomm y z]
      exact?
  have haddR (x y z : J) : x * (y + z) = x * y + x * z := by
    rw [hcomm x (y + z), haddL, hcomm y x, hcomm z x]
  have hsmulL (r : ℝ) (x y : J) : (r • x) * y = r • (x * y) := by
    first
    | exact smul_mul_assoc r x y
    | exact?
  have hsmulR (r : ℝ) (x y : J) : x * (r • y) = r • (x * y) := by
    rw [hcomm x (r • y), hsmulL, hcomm y x]
  have hunitL (x : J) : (1 : J) * x = x := by
    first
    | exact one_mul x
    | exact?
    | rw [hcomm]
      exact?
  have hunitR (x : J) : x * (1 : J) = x := by
    rw [hcomm, hunitL]
  have hinner (x y z : J) :
      inner ℝ (x * y) z = inner ℝ x (y * z) := by
    first
    | exact?
    | rw [hcomm x y]
      exact?
    | cases ‹EuclideanJordanAlgebra J› <;> aesop
  let L : J → J →ₗ[ℝ] J := fun x =>
    { toFun := fun y => x * y
      map_add' := fun y z => haddR x y z
      map_smul' := by
        intro r y
        change x * (r • y) = r • (x * y)
        exact hsmulR r x y }
  let B₀ : J →ₗ[ℝ] (J →L[ℝ] J) :=
    { toFun := fun x => ⟨L x, (L x).continuous_of_finiteDimensional⟩
      map_add' := by
        intro x y
        ext z
        exact haddL x y z
      map_smul' := by
        intro r x
        ext y
        change (r • x) * y = r • (x * y)
        exact hsmulL r x y }
  let B : J →L[ℝ] (J →L[ℝ] J) :=
    ⟨B₀, B₀.continuous_of_finiteDimensional⟩
  have hB (x y : J) : B x y = x * y := rfl
  let e₀ : J ≃ₗ[ℝ] J :=
    { toFun := fun x => (2 : ℝ) • x
      invFun := fun x => (1 / 2 : ℝ) • x
      left_inv := by
        intro x
        norm_num [smul_smul]
      right_inv := by
        intro x
        norm_num [smul_smul]
      map_add' := by
        intro x y
        exact smul_add _ _ _
      map_smul' := by
        intro r x
        simp [smul_smul, mul_comm] }
  let e : J ≃L[ℝ] J :=
    { toLinearEquiv := e₀
      continuous_toFun := by
        change Continuous (fun x : J => (2 : ℝ) • x)
        exact continuous_const.smul continuous_id
      continuous_invFun := by
        change Continuous (fun x : J => (1 / 2 : ℝ) • x)
        exact continuous_const.smul continuous_id }
  have hBd : HasStrictFDerivAt (fun x : J => B x) B (1 : J) := by
    first
    | exact B.hasStrictFDerivAt
    | exact B.hasStrictFDerivAt (1 : J)
  have hsq : HasStrictFDerivAt (fun x : J => x * x)
      (e : J →L[ℝ] J) (1 : J) := by
    have hs := hBd.clm_apply (hasStrictFDerivAt_id (𝕜 := ℝ) (1 : J))
    have he :
        (B (1 : J)).comp (ContinuousLinearMap.id ℝ J) + B.flip (1 : J) =
          (e : J →L[ℝ] J) := by
      apply ContinuousLinearMap.ext
      intro x
      change (1 : J) * x + x * (1 : J) = (2 : ℝ) • x
      rw [hunitL, hunitR, two_smul]
    first
    | simpa only [he] using hs
    | convert hs using 1 <;>
        first
        | rfl
        | ext x
          simp [B, B₀, L, e, e₀, hunitL, hunitR, two_smul]
  have hmap :
      Filter.map (fun x : J => x * x) (nhds (1 : J)) =
        nhds ((1 : J) * 1) := by
    exact HasStrictFDerivAt.map_nhds_eq_of_equiv hsq
  have hrange : Set.range (fun x : J => x * x) ∈ nhds (1 : J) := by
    have h :
        Set.range (fun x : J => x * x) ∈
          Filter.map (fun x : J => x * x) (nhds (1 : J)) := by
      change ∀ᶠ x : J in nhds (1 : J), ∃ y : J, y * y = x * x
      exact Filter.Eventually.of_forall fun x => ⟨x, rfl⟩
    rw [hmap] at h
    simpa only [hunitL] using h
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hrange
  have hlocal (x : J) (hx : ‖x‖ < δ) : Positive (1 + x) := by
    apply hball
    change dist (1 + x) (1 : J) < δ
    simpa [dist_eq_norm] using hx
  refine ⟨(1 / 2 : ℝ) • (1 : J), mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Metric.mem_nhds_iff.mpr
  refine ⟨δ / 2, by linarith, ?_⟩
  intro y hy
  have hy' : ‖(2 : ℝ) • (y - (1 / 2 : ℝ) • (1 : J))‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num at *
    rw [dist_eq_norm] at hy
    linarith
  have hp := hlocal ((2 : ℝ) • (y - (1 / 2 : ℝ) • (1 : J))) hy'
  have hm := hlocal (-((2 : ℝ) • (y - (1 / 2 : ℝ) • (1 : J)))) (by simpa using hy')
  have hscale (r : ℝ) (hr : 0 ≤ r) {x : J} (hx : Positive x) : Positive (r • x) := by
    obtain ⟨z, rfl⟩ := hx
    refine ⟨Real.sqrt r • z, ?_⟩
    simp only [hsmulL, hsmulR, smul_smul, Real.mul_self_sqrt hr]
  constructor
  · have heq : (1 / 2 : ℝ) • (1 + (2 : ℝ) • (y - (1 / 2 : ℝ) • (1 : J))) = y := by
      simp only [smul_add, smul_sub, smul_smul]
      module
    rw [← heq]
    exact hscale (1 / 2) (by norm_num) hp
  · change Positive (1 - y)
    have heq : (1 / 2 : ℝ) • (1 + -((2 : ℝ) • (y - (1 / 2 : ℝ) • (1 : J)))) = 1 - y := by
      simp only [smul_add, smul_sub, smul_smul, smul_neg]
      module
    rw [← heq]
    exact hscale (1 / 2) (by norm_num) hm


/-- complex_structure_exp: lem:orientation(iii), exponential identification. A complex structure exponentiates to its cosine-sine rotation. -/
theorem complex_structure_exp (D : J →L[ℝ] J) (h : D.comp D = -ContinuousLinearMap.id ℝ J) (t : ℝ) : NormedSpace.exp (t • D) = Real.cos t • ContinuousLinearMap.id ℝ J + Real.sin t • D := by
  exact complex_structure_exp_aux D h t

/-- aut_compact: §2.1; F5. The group of Jordan automorphisms is compact as a set of linear operators. -/
theorem aut_compact : IsCompact {f : J →L[ℝ] J | ∃ g : J ≃ₗ[ℝ] J, JordanAuto g ∧ ∀ x, f x = g x} := by
  sorry

/-- derivations_exponentiate: §2.1; F5 Lie algebra identification. A Jordan derivation exponentiates to Jordan automorphisms. -/
theorem derivations_exponentiate (D : J →L[ℝ] J) (hD : Derivation D.toLinearMap) (t : ℝ) : ∃ g : J ≃ₗ[ℝ] J, JordanAuto g ∧ ∀ x, g x = NormedSpace.exp (t • D) x := by
  let B : J →L[ℝ] J →L[ℝ] J :=
    ((LinearMap.toContinuousLinearMap : (J →ₗ[ℝ] J) ≃ₗ[ℝ] (J →L[ℝ] J)).toLinearMap.comp
      (jmulₗ J)).toContinuousLinearMap
  have hB (x y : J) : B x y = x * y := rfl
  have hmul (x y : J) : NormedSpace.exp (t • D) (x * y) =
      NormedSpace.exp (t • D) x * NormedSpace.exp (t • D) y := by
    simpa only [hB] using exp_bilinear_of_derivation B D (by intro a b; simpa only [hB, ContinuousLinearMap.coe_coe] using (hD a b)) x y t
  letI : NormedAlgebra ℚ (J →L[ℝ] J) := .restrictScalars ℚ ℝ _
  obtain ⟨u, hu⟩ := NormedSpace.isUnit_exp (t • D)
  let g : J ≃ₗ[ℝ] J := (ContinuousLinearEquiv.ofUnit u).toLinearEquiv
  have hg (x : J) : g x = NormedSpace.exp (t • D) x := by
    change (u : J →L[ℝ] J) x = _
    rw [hu]
  have hmulg (x y : J) : g (x * y) = g x * g y := by
    simpa only [hg] using hmul x y
  refine ⟨g, ⟨?_, hmulg⟩, hg⟩
  obtain ⟨x, hx⟩ := g.surjective 1
  have h := hmulg 1 x
  rw [EuclideanJordanAlgebra.one_mul, hx] at h
  simpa [EuclideanJordanAlgebra.one_mul, EuclideanJordanAlgebra.mul_comm] using h.symm

/-- model_inhabitance: §2.1 model list, concrete producer gate. Every admitted model label has a nonempty simple EJA realization. -/
theorem model_inhabitance (ℓ : Label) : ∃ A : Object, Simple A.V ∧ Realizes A.V ℓ := by
  sorry

/-- spin_low_rank_models: §2.2 low-rank identifications. Spin vector dimensions 2,3,5,9 realize the stated rank-two matrix models. -/
theorem spin_low_rank_models : ((Nonempty (SpinModel J 2)) → Nonempty (RealModel J 2)) ∧ ((Nonempty (SpinModel J 3)) → Nonempty (ComplexModel J 2)) ∧ ((Nonempty (SpinModel J 5)) → Nonempty (QuaternionModel J 2)) ∧ ((Nonempty (SpinModel J 9)) → Nonempty (MatrixModel J Oct octMul octConj octOne 2)) := by
  sorry

/-- spin_rotation_converse: §2.2 automorphism converse. Every orthogonal vector map preserves the spin product and the unit. -/
theorem spin_rotation_converse {d : ℕ} (O : Vec d ≃ₗᵢ[ℝ] Vec d) (a b : Spin d) : spinMul (a.1,O a.2) (b.1,O b.2) = ((spinMul a b).1,O (spinMul a b).2) := by
  ext <;> simp [spinMul]

/-- spin_s67: §5.2 S6-S7. Compatibility is closed under complement, admissible addition and spin product. -/
theorem spin_s67 {d : ℕ} (hd : 2 ≤ d) (A : AxisField d) (a b c : Spin d) (ha : spinEffect a) (hb : spinEffect b) (hc : spinEffect c) (hab : spinProduct A a b = spinProduct A b a) (hac : spinProduct A a c = spinProduct A c a) : spinProduct A a (spinUnit d-b) = spinProduct A (spinUnit d-b) a ∧ (spinEffect (b+c) → spinProduct A a (b+c) = spinProduct A (b+c) a) ∧ spinProduct A a (spinProduct A b c) = spinProduct A (spinProduct A b c) a := by
  sorry

/-- matrix_aut_types: rem:moduli, quotient by all automorphisms. Complex Jordan automorphisms are unitary conjugations or unitary conjugations after transpose. -/
theorem matrix_aut_types {n : ℕ} (M : ComplexModel J n) (hn : 2 ≤ n) (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) : ∃ u : Matrix (Fin n) (Fin n) ℂ, u*u.conjTranspose = 1 ∧ u.conjTranspose*u = 1 ∧ ((∀ x, M.map (g x) = u*M.map x*u.conjTranspose) ∨ (∀ x, M.map (g x) = u*(M.map x).transpose*u.conjTranspose)) := by
  sorry

/-- unitary_covariance: §6.3 weaker selectors; rem:moduli. Every twist is covariant under unitary conjugation. -/
theorem unitary_covariance {n : ℕ} (M : ComplexModel J n) (P : SequentialProduct J) (t : ℝ) (ht : Twist M t P.sp) (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) (u : Matrix (Fin n) (Fin n) ℂ) (hu : u*u.conjTranspose = 1) (hu2 : u.conjTranspose*u = 1) (hmap : ∀ x, M.map (g x) = u*M.map x*u.conjTranspose) (a b : J) (ha : IsEffect a) (hb : IsEffect b) : P.sp (g a) (g b) = g (P.sp a b) := by
  sorry

/-- atomic_transition_symmetry: §6.3 weaker selectors. Atomic transition trace symmetry holds for every twist and therefore does not select t. -/
theorem atomic_transition_symmetry {n : ℕ} (M : ComplexModel J n) (P : SequentialProduct J) (t : ℝ) (ht : Twist M t P.sp) (p q : J) (hp : Idempotent p) (hq : Idempotent q) : (Matrix.trace (M.map (P.sp p q))).re = (Matrix.trace (M.map p*M.map q)).re ∧ (Matrix.trace (M.map (P.sp p q))).re = (Matrix.trace (M.map (P.sp q p))).re := by
  sorry

/-- detection_specialization: rem:twist-detection, operational bridge. The explicit detection factor is the actual spectral twist factor for the diagonal first effect. -/
theorem detection_specialization (M : ComplexModel J 2) (a : J) (r t : ℝ) (hr : 0 < r) (ha : M.map a = detectionA r) : twistFactor M t a = detectionFactor t r := by
  have h := detection_cfc M a (fun x => Real.sqrt x * Real.cos (t * Real.log x)) r hr ha
  have h' := detection_cfc M a (fun x => Real.sqrt x * Real.sin (t * Real.log x)) r hr ha
  rw [twistFactor, h, h']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [detectionFactor, Real.log_exp, Matrix.smul_apply]
  rw [← Real.exp_half, Complex.ofReal_exp]
  rw [show (-(↑r / 2) - Complex.I * (↑t * ↑r) : ℂ) = ((↑(-r / 2) : ℂ) + (-(↑t * ↑r)) * Complex.I) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- central_coordinate_generator: prop:central-imaginary, full coordinate context. The block action of frame-fixing derivations has a single commuting imaginary coordinate generator. -/
theorem central_coordinate_generator {K : Type} [NonAssocRing K] [StarRing K] [Module ℝ K] [StarModule ℝ K] [SMulCommClass ℝ K K] [IsScalarTower ℝ K K] [Nontrivial K] {n : ℕ} (hn : 3 ≤ n) (M : MatrixModel J K (·*·) star 1 n) (re : K →ₗ[ℝ] ℝ) (hre : ∀ x, x+star x = (2*re x) • (1 : K)) (D : (Fin n → ℝ) →ₗ[ℝ] (J →ₗ[ℝ] J)) (hD : ∀ r, Derivation (D r)) (hfix : ∀ r i p, M.map p = coordDiag i → D r p = 0) (t : Fin n → Fin n → K →ₗ[ℝ] K) (ht : ∀ r i j x z, i ≠ j → M.map z = coordSlot star i j x → M.map (D r z) = (r i-r j) • coordSlot star i j (t i j x)) : ∃ γ : K, re γ = 0 ∧ (∀ x, γ*x = x*γ) ∧ ∀ i j, i ≠ j → ∀ x, t i j x = γ*x := by
  sorry

/-- trace_form: §2.1 trace form. The canonical Jordan trace form is positive definite and associative. -/
theorem trace_form : (∀ x : J, 0 ≤ jordanTrace (x*x)) ∧ (∀ x : J, jordanTrace (x*x) = 0 ↔ x = 0) ∧ ∀ x y z : J, jordanTrace ((x*y)*z) = jordanTrace (y*(x*z)) := by
  sorry

/-- support_unitary: eq:backaction-intro. The support-log phase is unitary even for singular effects, and multiplying it by sqrt(a) gives the twist factor. -/
theorem support_unitary {n : ℕ} (M : ComplexModel J n) (t : ℝ) (a : J) (ha : IsEffect a) : phaseUnit M t a*(phaseUnit M t a).conjTranspose = 1 ∧ (phaseUnit M t a).conjTranspose*phaseUnit M t a = 1 ∧ twistFactor M t a = M.map (sqrt a)*phaseUnit M t a := by
  sorry

/-- backaction: eq:backaction-intro; state operation. The effect twist is Luders followed by conjugation; its dual single-Kraus state operation has Born trace. -/
theorem backaction {n : ℕ} (M : ComplexModel J n) (P : SequentialProduct J) (t : ℝ) (ht : Twist M t P.sp) (a b : J) (ha : IsEffect a) (hb : IsEffect b) (ρ : Matrix (Fin n) (Fin n) ℂ) : M.map (P.sp a b) = adjointAction (phaseUnit M t a) (M.map (luders a b)) ∧ Matrix.trace ((phaseUnit M t a).conjTranspose*M.map (sqrt a)*ρ*M.map (sqrt a)*phaseUnit M t a) = Matrix.trace (M.map a*ρ) := by
  sorry

/-- moduli_isomorphism: rem:moduli, automorphism quotient. Two complex products are Jordan-isomorphic exactly when their parameters differ at most by sign. -/
theorem moduli_isomorphism {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n) (P R : SequentialProduct J) (s t : ℝ) (hs : Twist M s P.sp) (ht : Twist M t R.sp) : (∃ g : J ≃ₗ[ℝ] J, JordanAuto g ∧ ∀ a b, IsEffect a → IsEffect b → R.sp (g a) (g b) = g (P.sp a b)) ↔ t = s ∨ t = -s := by
  sorry

/-- frame_function_example: ex:frame-dependent, construction. The squared-axis function descends continuously to RP2. -/
theorem frame_function_example (ρ : Vec 3) (hρ : ‖ρ‖ = 1) : ∃ t : C(RP2, ℝ), ∀ v : sphere 3, t (rp2Class v) = (inner ℝ v.val ρ)^2 := by
  let f : sphere 3 → ℝ := fun v => (inner ℝ v.val ρ)^2
  have hf : ∀ a b : sphere 3, Antipodal.r a b → f a = f b := by
    intro a b hab
    rcases hab with hab | hab
    · simp [f, hab]
    · simp [f, hab]
  let g : RP2 → ℝ := Quotient.lift f hf
  have hg : Continuous g := by
    change @Continuous RP2 ℝ (TopologicalSpace.coinduced (Quotient.mk Antipodal) inferInstance) _ g
    apply continuous_coinduced_dom.mpr
    change Continuous f
    exact (continuous_subtype_val.inner continuous_const).pow 2
  exact ⟨⟨g, hg⟩, fun v => rfl⟩

/-- frame_nonconjugacy: ex:frame-dependent, nonconjugacy. The squared-axis product cannot be transported to any constant-twist product by a Jordan automorphism. -/
theorem frame_nonconjugacy (M : SpinModel J 3) (ρ : Vec 3) (hρ : ‖ρ‖ = 1) (t : C(RP2, ℝ)) (ht : ∀ v : sphere 3, t (rp2Class v) = (inner ℝ v.val ρ)^2) (c : ℝ) (g : J ≃ₗ[ℝ] J) (hg : JordanAuto g) : ¬ (∀ a b, IsEffect a → IsEffect b → spinOn M (fieldOfFrameFunction (ContinuousMap.const RP2 c)) (g a) (g b) = g (spinOn M (fieldOfFrameFunction t) a b)) := by
  sorry

/-- spin_zero_luders: def:spin-product, star_0. A field vanishing on the sphere gives precisely the Luders product. -/
theorem spin_zero_luders {d : ℕ} (M : SpinModel J d) (hd : 2 ≤ d) (A : AxisField d) (hA : ∀ v, ‖v‖ = 1 → A.A v = 0) : Agrees (spinOn M A) luders := by
  sorry

/-- pauli_product: §2.2 Pauli identification. The Pauli map preserves the Jordan product with the stated normalization. -/
theorem pauli_product (a b : Spin 3) : pauli (spinMul a b) = (1/2 : ℝ) • (pauli a*pauli b+pauli b*pauli a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, spinMul, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.sum_fin_eq_sum_range,
      Complex.ext_iff] <;> ring_nf <;> simp

/-- qubit_pauli_twist: cor:qubit-classification(ii), displayed formula. The signed spin generator produces the frame-dependent complex twist under the fixed Pauli identification. -/
theorem qubit_pauli_twist (S : SpinModel J 3) (M : ComplexModel J 2) (hM : ∀ x, M.map x = pauli (S.equiv x)) (t : C(RP2, ℝ)) (a b : J) (ha : IsEffect a) (hb : IsEffect b) (v : sphere 3) (lp lm : ℝ) (hdata : S.equiv a = lp • spinAtom v.val + lm • spinAtom (-v.val)) (hn : lp ≠ lm) : M.map (spinOn S (fieldOfFrameFunction t) a b) = twistFactor M (t (rp2Class v)) a*M.map b*(twistFactor M (t (rp2Class v)) a).conjTranspose := by
  sorry

end PaperA

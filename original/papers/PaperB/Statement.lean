import Mathlib.Algebra.Jordan.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Paper B: spectral compressions and Euclidean Jordan structure

Setting C of Paper B §2.1, the Jordan reconstruction statement, and the
homogeneity and rank-two theorems.

Manuscript: B. Ehrlich, *Positivity of the Canonical Compression Product Forces Jordan Structure* (in preparation).
-/

noncomputable section

namespace PaperB

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The ordered vector space and its designated compressions. The cone induces
the order `x ≤ y` when `y - x` belongs to it. -/
structure CompressionData (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  cone : ProperCone ℝ V
  pointed : ∀ ⦃x : V⦄, x ∈ cone → -x ∈ cone → x = 0
  generating : ∀ x : V, ∃ y ∈ cone, ∃ z ∈ cone, x = y - z
  e : V
  unit_pos : e ∈ cone
  orderUnit : ∀ x : V, ∃ r : ℝ, 0 < r ∧ r • e - x ∈ cone
  archimedean : ∀ x : V, (∀ ε : ℝ, 0 < ε → x + ε • e ∈ cone) → x ∈ cone
  P : Set V
  projective_effect : ∀ ⦃p⦄, p ∈ P → p ∈ cone ∧ e - p ∈ cone
  zero_projective : (0 : V) ∈ P
  unit_projective : e ∈ P
  complement : ∀ ⦃p⦄, p ∈ P → e - p ∈ P
  orthogonal_sum : ∀ ⦃p q⦄, p ∈ P → q ∈ P → e - (p + q) ∈ cone → p + q ∈ P
  C : {p // p ∈ P} → V →ₗ[ℝ] V
  positive : ∀ p ⦃x : V⦄, x ∈ cone → C p x ∈ cone
  idempotent : ∀ p, (C p).comp (C p) = C p
  image_unit : ∀ p, C p e = (p : V)
  compress_zero : C ⟨0, zero_projective⟩ = 0
  compress_unit : C ⟨e, unit_projective⟩ = LinearMap.id
  focus : ∀ (p : {p // p ∈ P}) ⦃b : V⦄, b ∈ cone → (p : V) - b ∈ cone → C p b = b
  kernel : ∀ p ⦃b : V⦄, b ∈ cone → e - b ∈ cone → C p b = 0 → e - p - b ∈ cone

/-- The order interval `[0,e]` for the given cone and unit. -/
def CompressionData.IsEffect (D : CompressionData V) (a : V) : Prop :=
  a ∈ D.cone ∧ D.e - a ∈ D.cone

/-- A projective resolution of the unit, with zero summands omitted. Positivity
and the sum condition imply order orthogonality for every pair of distinct indices. -/
structure ProjectiveFrame (D : CompressionData V) (n : ℕ) where
  p : Fin n → {p // p ∈ D.P}
  nonzero : ∀ i, (p i : V) ≠ 0
  sum_eq_unit : ∑ i, (p i : V) = D.e

namespace ProjectiveFrame

variable {D : CompressionData V} {n : ℕ} (F : ProjectiveFrame D n)

/-- The sum of any subfamily of a frame is projective. -/
theorem sum_mem_projective (s : Finset (Fin n)) : (∑ i ∈ s, (F.p i : V)) ∈ D.P := by
  have complement_pos (t : Finset (Fin n)) : D.e - ∑ i ∈ t, (F.p i : V) ∈ D.cone := by
    have hsum :
        (∑ i ∈ Finset.univ \ t, (F.p i : V)) + ∑ i ∈ t, (F.p i : V) = D.e :=
      (Finset.sum_sdiff (Finset.subset_univ t)).trans F.sum_eq_unit
    rw [← hsum, add_sub_cancel_right]
    exact D.cone.toSubmodule.sum_mem fun i _ ↦ (D.projective_effect (F.p i).property).1
  induction s using Finset.induction_on with
  | empty => simpa using D.zero_projective
  | @insert i s hi hs =>
    rw [Finset.sum_insert hi]
    exact D.orthogonal_sum (F.p i).property hs (by
      simpa only [Finset.sum_insert hi] using complement_pos (insert i s))

/-- Compression at the projective unit obtained by joining the selected summands. -/
def sumCompression (s : Finset (Fin n)) : V →ₗ[ℝ] V :=
  D.C ⟨∑ i ∈ s, (F.p i : V), F.sum_mem_projective s⟩

/-- The mixed Peirce projection. The Peirce formulas use it only when `i < j`. -/
def peircePair (i j : Fin n) : V →ₗ[ℝ] V :=
  F.sumCompression {i, j} - D.C (F.p i) - D.C (F.p j)

/-- Index the diagonal projections by the frame and the mixed ones by unordered pairs. -/
def peirceMap : (Fin n ⊕ {ij : Fin n × Fin n // ij.1 < ij.2}) → V →ₗ[ℝ] V
  | .inl i => D.C (F.p i)
  | .inr ij => F.peircePair ij.val.1 ij.val.2

/-- Sum the diagonal and mixed projections internal to a subset of the frame. -/
def peirceSum (s : Finset (Fin n)) : V →ₗ[ℝ] V :=
  (∑ i ∈ s, D.C (F.p i)) +
    ∑ i ∈ s, ∑ j ∈ s.filter (i < ·), F.peircePair i j

/-- H-P on this frame, including coarsening by every subset. -/
def HasPeirceDecomposition : Prop :=
  (∀ k, (F.peirceMap k).comp (F.peirceMap k) = F.peirceMap k) ∧
  (∀ k l, k ≠ l → (F.peirceMap k).comp (F.peirceMap l) = 0) ∧
  F.peirceSum Finset.univ = LinearMap.id ∧
  ∀ s, F.sumCompression s = F.peirceSum s

end ProjectiveFrame

/-- An orthogonal projective expansion of an effect. Equal coefficients are
allowed until the expansion is coarsened to its canonical resolution. -/
structure SpectralExpansion (D : CompressionData V) (a : V) where
  n : ℕ
  frame : ProjectiveFrame D n
  coeff : Fin n → ℝ
  coeff_mem : ∀ i, coeff i ∈ Set.Icc (0 : ℝ) 1
  sum_eq : ∑ i, coeff i • (frame.p i : V) = a

/-- The spectral compression data of Setting C, including the full multiframe H-P. -/
structure SpectralCompressionSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] extends CompressionData V where
  canonical : ∀ {a : V}, toCompressionData.IsEffect a → SpectralExpansion toCompressionData a
  canonical_distinct : ∀ {a : V} (ha : toCompressionData.IsEffect a),
    Function.Injective (canonical ha).coeff
  canonical_unique : ∀ {a : V} (ha : toCompressionData.IsEffect a)
    (G : SpectralExpansion toCompressionData a), Function.Injective G.coeff →
    ∃ σ : Fin (canonical ha).n ≃ Fin G.n, ∀ i,
      (canonical ha).coeff i = G.coeff (σ i) ∧ (canonical ha).frame.p i = G.frame.p (σ i)
  canonical_coarsening : ∀ {a : V} (ha : toCompressionData.IsEffect a)
    (G : SpectralExpansion toCompressionData a),
    Set.range G.coeff = Set.range (canonical ha).coeff ∧
    ∀ i, ((canonical ha).frame.p i : V) =
      ∑ j ∈ Finset.univ.filter (fun j => G.coeff j = (canonical ha).coeff i), (G.frame.p j : V)
  peirce : ∀ {n : ℕ} (F : ProjectiveFrame toCompressionData n), F.HasPeirceDecomposition

variable [FiniteDimensional ℝ V]

/-- The canonical compression formula on a spectral resolution of an effect. -/
def canonicalK (S : SpectralCompressionSpace V) {a : V} (ha : S.IsEffect a) : V →ₗ[ℝ] V :=
  let R := S.canonical ha
  (∑ i, R.coeff i • S.C (R.frame.p i)) +
    ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
      Real.sqrt (R.coeff i * R.coeff j) • R.frame.peircePair i j

/-- Positivity of every canonical update, the cone formulation of H-E. -/
def HE (S : SpectralCompressionSpace V) : Prop :=
  ∀ ⦃a : V⦄ (ha : S.IsEffect a) ⦃b : V⦄, b ∈ S.cone → canonicalK S ha b ∈ S.cone

/-- The square root obtained by taking square roots of the canonical coefficients. -/
def spectralSqrt (S : SpectralCompressionSpace V) {a : V} (ha : S.IsEffect a) : V :=
  let R := S.canonical ha
  ∑ i, Real.sqrt (R.coeff i) • (R.frame.p i : V)

/-- A unital commutative Jordan product over ℝ that is formally real. -/
def IsEuclideanJordan (m : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : V) : Prop :=
  ∃ comm : ∀ x y, m x y = m y x,
    (letI : CommMagma V := { mul := fun x y => m x y, mul_comm := comm }
     IsCommJordan V) ∧
    (∀ x, m e x = x) ∧
    ∀ (n : ℕ) (x : Fin n → V), (∑ i, m (x i) (x i)) = 0 → ∀ i, x i = 0

/-- The quadratic representation `Uₓ = 2 Lₓ² - L_{x²}`. -/
def quadraticRepresentation (m : V →ₗ[ℝ] V →ₗ[ℝ] V) (x : V) : V →ₗ[ℝ] V :=
  (2 : ℝ) • (m x).comp (m x) - m (m x x)

/-- In Setting C, H-E forces a Euclidean Jordan product with the given cone,
projective units, compressions, and canonical updates. -/
theorem paperB (S : SpectralCompressionSpace V) (h : HE S) :
    ∃ m : V →ₗ[ℝ] V →ₗ[ℝ] V,
      IsEuclideanJordan m S.e ∧
      (S.cone : Set V) = Set.range (fun x => m x x) ∧
      (∀ p, p ∈ S.P ↔ m p p = p) ∧
      (∀ p, S.C p = quadraticRepresentation m p) ∧
      ∀ (a : V) (ha : S.IsEffect a),
        spectralSqrt S ha ∈ S.cone ∧
        m (spectralSqrt S ha) (spectralSqrt S ha) = a ∧
        canonicalK S ha = quadraticRepresentation m (spectralSqrt S ha) := by
  sorry

/-- Theorem 4: the linear cone automorphism group is transitive on the interior. -/
theorem homogeneous_of_HE (S : SpectralCompressionSpace V) (h : HE S) :
    ∀ x ∈ interior (S.cone : Set V), ∀ y ∈ interior (S.cone : Set V),
      ∃ g : V ≃ₗ[ℝ] V, (∀ v, g v ∈ S.cone ↔ v ∈ S.cone) ∧ g x = y := by
  sorry

/-- Rank two means the maximum cardinality of a frame is two. -/
def IsRankTwo (D : CompressionData V) : Prop :=
  Nonempty (ProjectiveFrame D 2) ∧ ∀ n, ProjectiveFrame D n → n ≤ 2

/-- The standard Lorentz cone on the real spin-factor space. -/
def lorentzCone (n : ℕ) : Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
  {x | ‖x.2‖ ≤ x.1}

/-- Theorem 5: in rank two and real dimension at least three, H-E characterizes
Lorentz cones up to linear isomorphism. -/
theorem rankTwo_HE_iff_lorentz (S : SpectralCompressionSpace V)
    (hrank : IsRankTwo S.toCompressionData) (hdim : 3 ≤ Module.finrank ℝ V) :
    HE S ↔
      ∃ g : V ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ V - 1))),
        ∀ x, g x ∈ lorentzCone (Module.finrank ℝ V - 1) ↔ x ∈ S.cone := by
  sorry

/-- Non-vacuity: the standard spin-factor cone and unit carry Setting C and H-E. -/
theorem spinFactor_satisfies_HE (n : ℕ) :
    ∃ S : SpectralCompressionSpace (ℝ × EuclideanSpace ℝ (Fin n)),
      (S.cone : Set _) = lorentzCone n ∧ S.e = (1, 0) ∧ HE S := by
  sorry

/-- The cone in the rank-two example with coherence interval `[-1,2]`.
Coordinates are `(t, σ, w)`. -/
def asymmetricCone : Set (ℝ × ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧
    (0 ≤ x.2.2 → x.2.1 ^ 2 + x.2.2 ^ 2 / 4 ≤ x.1 ^ 2) ∧
    (x.2.2 ≤ 0 → x.2.1 ^ 2 + x.2.2 ^ 2 ≤ x.1 ^ 2)}

/-- Discrimination: the explicit transverse update in §3.3 violates H-E. -/
theorem asymmetricCone_fails_HE :
    ∃ S : SpectralCompressionSpace (ℝ × ℝ × ℝ),
      (S.cone : Set _) = asymmetricCone ∧ S.e = (1, 0, 0) ∧
      IsRankTwo S.toCompressionData ∧ ¬ HE S ∧
      ∃ r q : {p // p ∈ S.P},
        (r : ℝ × ℝ × ℝ) = (2 / 3, 0, -(2 / 3)) ∧
        (q : ℝ × ℝ × ℝ) = (1 / 3, 0, 2 / 3) ∧
        (∀ x : ℝ × ℝ × ℝ, S.C r x = (x.1 - x.2.2 / 2) • (r : ℝ × ℝ × ℝ)) ∧
        (∀ x : ℝ × ℝ × ℝ, S.C q x = (x.1 + x.2.2) • (q : ℝ × ℝ × ℝ)) ∧
        ∃ (ha : S.IsEffect (1 / 2, 0, 1 / 2)) (_hb : S.IsEffect (1 / 2, 1 / 2, 0)),
          canonicalK S ha (1 / 2, 1 / 2, 0) = (1 / 4, 1 / 4, 1 / 4) ∧
          canonicalK S ha (1 / 2, 1 / 2, 0) ∉ S.cone := by
  sorry

end PaperB

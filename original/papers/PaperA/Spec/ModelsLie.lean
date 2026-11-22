import PaperA.Claims
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! Manuscript §2.1 models and automorphism interfaces. Later proofs are separate
from the original theorem population. No associativity is imposed on octonions. -/
noncomputable section
open EuclideanJordan
open scoped Manifold ContDiff
namespace PaperA.Spec.ModelsLie

variable (J : Type) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J]

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:300-301: "and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$."
The actual unital Jordan automorphisms, with composition as multiplication. -/
def automorphisms : Subgroup (J ≃L[ℝ] J) where
  carrier := {g | JordanAuto g.toLinearEquiv}
  one_mem' := ⟨rfl, fun _ _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨gu, gm⟩ ⟨hu, hm⟩
    change g 1 = 1 at gu
    change h 1 = 1 at hu
    change ∀ x y, g (x*y) = g x * g y at gm
    change ∀ x y, h (x*y) = h x * h y at hm
    exact ⟨by change g (h 1) = 1; rw [hu, gu],
      fun x y => by change g (h (x*y)) = g (h x) * g (h y); rw [hm, gm]⟩
  inv_mem' := by
    rintro g ⟨gu, gm⟩
    change g 1 = 1 at gu
    change ∀ x y, g (x*y) = g x * g y at gm
    change g.symm 1 = 1 ∧ ∀ x y, g.symm (x*y) = g.symm x * g.symm y
    constructor
    · apply g.injective
      rw [g.apply_symm_apply, gu]
    · intro x y
      apply g.injective
      rw [g.apply_symm_apply, gm, g.apply_symm_apply, g.apply_symm_apply]

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:300-301: "compact Lie group with Lie algebra the derivations".
The subspace topology is inherited from continuous linear equivalences. -/
abbrev Aut := ↥(automorphisms J)

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:300-301: "Lie algebra the derivations $\operatorname{Der}(J)$".
Jordan derivations as a concrete real subspace of continuous operators. -/
def derivations : Submodule ℝ (J →L[ℝ] J) where
  carrier := {D | Derivation D.toLinearMap}
  zero_mem' := by intro x y; simp
  add_mem' := by
    intro D E hD hE x y
    change ∀ x y, D (x*y) = D x*y + x*D y at hD
    change ∀ x y, E (x*y) = E x*y + x*E y at hE
    change D (x*y) + E (x*y) = (D x+E x)*y + x*(D y+E y)
    rw [hD, hE, add_mul, mul_add]
    abel
  smul_mem' := by
    intro r D hD x y
    change ∀ x y, D (x*y) = D x*y + x*D y at hD
    change r • D (x*y) = (r • D x)*y + x*(r • D y)
    rw [hD, smul_add, smul_mul_assoc, mul_smul_comm]

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:300-301: "compact Lie group with Lie algebra the derivations".
Faithful inclusion into the operator space; its norm is the operator norm. -/
def operator (g : Aut J) : J →L[ℝ] J := g.val.toContinuousLinearMap

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


The topology induced by the faithful inclusion into the operator-norm space. -/
instance autTopology : TopologicalSpace (Aut J) :=
  TopologicalSpace.induced (operator J) inferInstance

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:300-301: "and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$."
A finite dimensional smooth atlas on the actual group. The differential of
its operator inclusion is a linear equivalence onto Jordan derivations, and
carries the tangent Lie bracket to the operator commutator. The topology is
the fixed subspace topology, never a topology supplied as a hypothesis. -/
-- LATER_PROOF: compact_lie_identification
theorem compact_lie_identification :
    ∃ charts : ChartedSpace (derivations J) (Aut J),
      letI := charts
      IsManifold 𝓘(ℝ, derivations J) ∞ (Aut J) ∧
      CompactSpace (Aut J) ∧
      LieGroup 𝓘(ℝ, derivations J) ∞ (Aut J) ∧
      ContMDiff 𝓘(ℝ, derivations J) 𝓘(ℝ, J →L[ℝ] J) ∞ (operator J) ∧
      ∃ e : GroupLieAlgebra 𝓘(ℝ, derivations J) (Aut J) ≃ₗ[ℝ] derivations J,
        (∀ v, (e v).val =
          mfderiv 𝓘(ℝ, derivations J) 𝓘(ℝ, J →L[ℝ] J) (operator J) 1 v) ∧
        (∀ v w, (e ⁅v, w⁆).val =
          (e v).val.comp (e w).val - (e w).val.comp (e v).val) := by
  sorry

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:300-301: "compact Lie group with Lie algebra the derivations".
The continuous one-parameter interface uses the real topology on time and the
operator-norm topology on operators. It derives the Jordan derivation law,
with no differentiability assumption on the curve. -/
-- LATER_PROOF: one_parameter_derivation
theorem one_parameter_derivation (φ : ℝ → J →L[ℝ] J)
    (hc : Continuous φ) (h0 : φ 0 = ContinuousLinearMap.id ℝ J)
    (hm : ∀ s t, φ (s+t) = (φ s).comp (φ t))
    (ha : ∀ t, ∃ g : Aut J, operator J g = φ t) :
    ∃! D : J →L[ℝ] J, Derivation D.toLinearMap ∧
      (∀ t, φ t = NormedSpace.exp (t • D)) ∧
      HasDerivAt φ D 0 := by
  sorry

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:299-300: "When $J$ is simple,
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity)".
Concrete off-diagonal simultaneous eigenspace, over the real numbers. -/
def blockSpace {n : ℕ} (F : JordanFrame J n) (i j : Fin n) : Submodule ℝ J where
  carrier := Block F i j
  zero_mem' := by constructor <;> simp
  add_mem' := by
    rintro x y ⟨hi, hj⟩ ⟨ki, kj⟩
    constructor <;> simp_all [mul_add, smul_add]
  smul_mem' := by
    rintro r x ⟨hi, hj⟩
    constructor
    · change F.p i * (r • x) = (1/2 : ℝ) • (r • x)
      rw [mul_smul_comm, hi, smul_comm r (1/2 : ℝ)]
    · change F.p j * (r • x) = (1/2 : ℝ) • (r • x)
      rw [mul_smul_comm, hj, smul_comm r (1/2 : ℝ)]

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:299-300: "When $J$ is simple,
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity)".
Any two frames and any two off-diagonal pairs, including reversed indices. -/
-- LATER_PROOF: peirce_dimensions_equal
theorem peirce_dimensions_equal (hJ : Simple J) {n m : ℕ}
    (F : JordanFrame J n) (G : JordanFrame J m)
    (i j : Fin n) (k l : Fin m) (hij : i ≠ j) (hkl : k ≠ l) :
    Module.finrank ℝ (blockSpace J F i j) =
      Module.finrank ℝ (blockSpace J G k l) := by
  sorry

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:302-307: "$H_3(\mathbb{O})$; ... The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$."
Real matrix models, any frame; the rank-three guard is explicit. -/
-- LATER_PROOF: real_peirce_dimension
theorem real_peirce_dimension {n r : ℕ} (hn : 3 ≤ n) (M : RealModel J n)
    (F : JordanFrame J r) (i j : Fin r) (hij : i ≠ j) :
    Module.finrank ℝ (blockSpace J F i j) = 1 := by
  sorry

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:302-307: "$H_3(\mathbb{O})$; ... The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$."
Complex matrix models, any frame. -/
-- LATER_PROOF: complex_peirce_dimension
theorem complex_peirce_dimension {n r : ℕ} (hn : 3 ≤ n) (M : ComplexModel J n)
    (F : JordanFrame J r) (i j : Fin r) (hij : i ≠ j) :
    Module.finrank ℝ (blockSpace J F i j) = 2 := by
  sorry

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:302-307: "$H_3(\mathbb{O})$; ... The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$."
Quaternion matrix models, any frame. -/
-- LATER_PROOF: quaternion_peirce_dimension
theorem quaternion_peirce_dimension {n r : ℕ} (hn : 3 ≤ n) (M : QuaternionModel J n)
    (F : JordanFrame J r) (i j : Fin r) (hij : i ≠ j) :
    Module.finrank ℝ (blockSpace J F i j) = 4 := by
  sorry

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:302-307: "$H_3(\mathbb{O})$; ... The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$."
AlbertModel fixes n=3 and uses the nonassociative octMul on division octonions. -/
-- LATER_PROOF: albert_peirce_dimension
theorem albert_peirce_dimension {r : ℕ} (M : AlbertModel J)
    (F : JordanFrame J r) (i j : Fin r) (hij : i ≠ j) :
    Module.finrank ℝ (blockSpace J F i j) = 8 := by
  sorry

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:302-305: "The simple EJAs are $\mathbb{R}$; ...
$H_3(\mathbb{O})$; and the spin factors $V_d$, $d \geq 2$, ... rank two".
Labels include real n≥2, complex/quaternion n≥3; V₂ uses real 2. -/
def labelRank : Label → ℕ
  | .scalar => 1
  | .real n _ => n
  | .complex n _ => n
  | .quaternion n _ => n
  | .albert => 3
  | .spin _ _ => 2

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


paper/main.tex:302-305: "The simple EJAs are $\mathbb{R}$; ...
$H_3(\mathbb{O})$; and the spin factors $V_d$, $d \geq 2$, ... rank two".
Compatibility for an arbitrary model witness, not a selected witness. -/
-- LATER_PROOF: model_rank
theorem model_rank (ℓ : Label) (W : ModelWitness J ℓ) :
    EuclideanJordan.rank J = labelRank ℓ := by
  sorry

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


Exponentiation as a continuous one-parameter subgroup in the fixed operator
subspace topology. Its value at zero and composition law are explicit. -/
-- LATER_PROOF: derivation_flow
theorem derivation_flow (D : J →L[ℝ] J) (hD : Derivation D.toLinearMap) :
    ∃ φ : ℝ → Aut J, Continuous φ ∧ φ 0 = 1 ∧
      (∀ s t, φ (s+t) = φ s * φ t) ∧
      (∀ t, operator J (φ t) = NormedSpace.exp (t • D)) := by
  classical
  letI : NormedAlgebra ℚ (J →L[ℝ] J) := .restrictScalars ℚ ℝ _
  choose g hg h_exp using PaperA.derivations_exponentiate D hD
  let φ : ℝ → Aut J := fun t => ⟨(g t).toContinuousLinearEquiv, hg t⟩
  have hφ (t : ℝ) : operator J (φ t) = NormedSpace.exp (t • D) := by
    ext x
    exact h_exp t x
  have h_ext {a b : Aut J} (h : operator J a = operator J b) : a = b := by
    apply Subtype.ext
    ext x
    exact congrArg (fun f : J →L[ℝ] J => f x) h
  refine ⟨φ, ?_, ?_, ?_, hφ⟩
  · apply continuous_induced_rng.mpr
    change Continuous (fun t => operator J (φ t))
    simp_rw [hφ]
    exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  · apply h_ext
    rw [hφ]
    simp [operator, NormedSpace.exp_zero]
  · intro s t
    apply h_ext
    change operator J (φ (s + t)) = (operator J (φ s)) * (operator J (φ t))
    rw [hφ, hφ, hφ, add_smul]
    exact NormedSpace.exp_add_of_commute (((Commute.refl D).smul_left s).smul_right t)

/-- Frozen manuscript 8f389ac87f52df9d28572dbef994d9f03bb9bb33, paper/main.tex:299-307:
$\dim V_{ij}$ is the same for all $i < j$ (the Peirce multiplicity), all Jordan frames are conjugate
under $\Aut(J)$~\cite[Thm.~IV.2.5]{FarautKoranyi1994}, and $\Aut(J)$ is a
compact Lie group with Lie algebra the derivations $\operatorname{Der}(J)$.  The
simple EJAs are $\mathbb{R}$; $\MnKsa{n}{\mathbb{K}} = H_n(\mathbb{K})$ for
$\mathbb{K} = \mathbb{R}, \mathbb{C}, \mathbb{H}$ and $n \geq 3$; $H_3(\mathbb{O})$;
and the spin factors $V_d$, $d \geq 2$, which are the simple EJAs of rank
two~\cite{JordanVonNeumannWigner1934,FarautKoranyi1994}.  The rank-at-least-three
types have Peirce multiplicity $1, 2, 4, 8$.


A bare finite-dimensional EJA produces a decomposition, legal labels, actual
model witnesses, and rank compatibility together. The zero algebra permits
an empty decomposition. This combines retained producers and adds no original
proof credit; it inherits their admissions and the new rank proof target. -/
theorem decomposition_models :
    ∃ D : Decomposition J, ∃ ℓ : Fin D.n → Label,
      ∃ W : ∀ i, ModelWitness (D.blocks i).V (ℓ i),
        ∀ i, EuclideanJordan.rank (D.blocks i).V = labelRank (ℓ i) := by
  classical
  obtain ⟨D⟩ := PaperA.simple_decomposition (J := J)
  have models (i : Fin D.n) : ∃ ℓ : Label, Nonempty (ModelWitness (D.blocks i).V ℓ) := by
    obtain ⟨ℓ, h⟩ := PaperA.jvnw (D.simple i)
    exact ⟨ℓ, by cases ℓ <;> exact h⟩
  choose ℓ hℓ using models
  let W : ∀ i, ModelWitness (D.blocks i).V (ℓ i) := fun i => Classical.choice (hℓ i)
  exact ⟨D, ℓ, W, fun i => model_rank (D.blocks i).V (ℓ i) (W i)⟩

end PaperA.Spec.ModelsLie

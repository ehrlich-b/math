import PaperA.Claims

/-! Operational specification interfaces. Existing statements are retained in
`PaperA.Claims`; the marked theorem bodies are additional proof obligations.
No statement elaboration here closes an original proof target. -/
noncomputable section
open scoped BigOperators
open EuclideanJordan
namespace PaperA.Spec.Observations

variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J]

/-- paper/main.tex:1372-1380 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
setting $\phi$; perform the unsharp two-outcome measurement of $a_r$, whose
strength sets $r$; then measure in the basis $\lvert\pm\rangle$.  Reading
$\seqp{a}{b}$ as ``$a$, then $b$,'' $p_t(r, \phi)$ is the relative frequency of the
outcome pair (yes, $+$).  Scanning the state phase isolates two quadratures,
$p_t(r,0)\propto\cos(tr)$ and $p_t(r,\tfrac\pi2)\propto\sin(tr)$ above the
$t$-independent pedestal $\tfrac14(1+e^{-r})$.  A single unsharp $r>0$ fixes $t$
modulo $2\pi/r$, and two values with irrational ratio fix $t$ in the noiseless
model.  Unsharpness is essential, by \Cref{cor:sharp}.  Liu and Wu already
compute the qubit form of their product and read $t$ as a physical ``time

The pedestal is retained and the amplitude is strictly positive.
-/
-- LATER_PROOF: detection_quadratures
theorem detection_quadratures (t r : ℝ) (hr : 0 < r) :
    detection t r 0 = (1 + Real.exp (-r))/4 + Real.exp (-r/2)/2 * Real.cos (t*r) ∧
    detection t r (Real.pi/2) = (1 + Real.exp (-r))/4 + Real.exp (-r/2)/2 * Real.sin (t*r) ∧
    0 < Real.exp (-r/2)/2 := by
  constructor
  · simp [detection, Real.cos_neg]
  constructor
  · simp [detection, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
  · positivity

/-- paper/main.tex:1372-1380 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
setting $\phi$; perform the unsharp two-outcome measurement of $a_r$, whose
strength sets $r$; then measure in the basis $\lvert\pm\rangle$.  Reading
$\seqp{a}{b}$ as ``$a$, then $b$,'' $p_t(r, \phi)$ is the relative frequency of the
outcome pair (yes, $+$).  Scanning the state phase isolates two quadratures,
$p_t(r,0)\propto\cos(tr)$ and $p_t(r,\tfrac\pi2)\propto\sin(tr)$ above the
$t$-independent pedestal $\tfrac14(1+e^{-r})$.  A single unsharp $r>0$ fixes $t$
modulo $2\pi/r$, and two values with irrational ratio fix $t$ in the noiseless
model.  Unsharpness is essential, by \Cref{cor:sharp}.  Liu and Wu already
compute the qubit form of their product and read $t$ as a physical ``time

Equality is equality of the two observed probabilities, not just a cosine.
-/
-- LATER_PROOF: detection_single_strength_iff
theorem detection_single_strength_iff (t s r : ℝ) (hr : 0 < r) :
    (detection t r 0 = detection s r 0 ∧
      detection t r (Real.pi/2) = detection s r (Real.pi/2)) ↔
    ∃ k : ℤ, t-s = (k : ℝ) * (2*Real.pi/r) := by
  have ht := detection_quadratures t r hr
  have hs := detection_quadratures s r hr
  have ha : Real.exp (-r/2)/2 ≠ 0 := ne_of_gt ht.2.2
  have hr0 : r ≠ 0 := ne_of_gt hr
  constructor
  · rintro ⟨h0, h90⟩
    rw [ht.1, hs.1] at h0
    rw [ht.2.1, hs.2.1] at h90
    have hc := (mul_left_cancel₀ ha) (add_left_cancel h0)
    have hsin := (mul_left_cancel₀ ha) (add_left_cancel h90)
    have hcos : Real.cos (t*r - s*r) = 1 := by
      rw [Real.cos_sub, hc, hsin]
      nlinarith [Real.sin_sq_add_cos_sq (s*r)]
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).1 hcos
    refine ⟨k, ?_⟩
    apply (mul_right_cancel₀ hr0)
    calc
      (t - s) * r = t*r - s*r := by ring
      _ = (k : ℝ) * (2 * Real.pi) := hk.symm
      _ = ((k : ℝ) * (2 * Real.pi / r)) * r := by field_simp
  · rintro ⟨k, hk⟩
    have htr : t*r = s*r + (k : ℝ) * (2*Real.pi) := by
      have h := congrArg (fun x : ℝ => x * r) hk
      field_simp at h
      nlinarith [h]
    constructor
    · rw [ht.1, hs.1, htr, Real.cos_add_int_mul_two_pi]
    · rw [ht.2.1, hs.2.1, htr, Real.sin_add_int_mul_two_pi]

/-- paper/main.tex:1372-1380 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
setting $\phi$; perform the unsharp two-outcome measurement of $a_r$, whose
strength sets $r$; then measure in the basis $\lvert\pm\rangle$.  Reading
$\seqp{a}{b}$ as ``$a$, then $b$,'' $p_t(r, \phi)$ is the relative frequency of the
outcome pair (yes, $+$).  Scanning the state phase isolates two quadratures,
$p_t(r,0)\propto\cos(tr)$ and $p_t(r,\tfrac\pi2)\propto\sin(tr)$ above the
$t$-independent pedestal $\tfrac14(1+e^{-r})$.  A single unsharp $r>0$ fixes $t$
modulo $2\pi/r$, and two values with irrational ratio fix $t$ in the noiseless
model.  Unsharpness is essential, by \Cref{cor:sharp}.  Liu and Wu already
compute the qubit form of their product and read $t$ as a physical ``time

Two quadratures imply equality at every phase at the same strength.
-/
-- LATER_PROOF: detection_two_quadratures
theorem detection_two_quadratures (t s r : ℝ) (hr : 0 < r)
    (h0 : detection t r 0 = detection s r 0)
    (h90 : detection t r (Real.pi/2) = detection s r (Real.pi/2)) :
    ∀ φ : ℝ, detection t r φ = detection s r φ := by
  have ht := detection_quadratures t r hr
  have hs := detection_quadratures s r hr
  have hc : Real.cos (t*r) = Real.cos (s*r) := by
    rw [ht.1, hs.1] at h0
    have ha : Real.exp (-r/2)/2 ≠ 0 := ne_of_gt ht.2.2
    exact (mul_left_cancel₀ ha) (add_left_cancel h0)
  have hsin : Real.sin (t*r) = Real.sin (s*r) := by
    rw [ht.2.1, hs.2.1] at h90
    have ha : Real.exp (-r/2)/2 ≠ 0 := ne_of_gt ht.2.2
    exact (mul_left_cancel₀ ha) (add_left_cancel h90)
  intro φ
  simp [detection, Real.cos_sub, hc, hsin]

/-- paper/main.tex:1372-1380 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
setting $\phi$; perform the unsharp two-outcome measurement of $a_r$, whose
strength sets $r$; then measure in the basis $\lvert\pm\rangle$.  Reading
$\seqp{a}{b}$ as ``$a$, then $b$,'' $p_t(r, \phi)$ is the relative frequency of the
outcome pair (yes, $+$).  Scanning the state phase isolates two quadratures,
$p_t(r,0)\propto\cos(tr)$ and $p_t(r,\tfrac\pi2)\propto\sin(tr)$ above the
$t$-independent pedestal $\tfrac14(1+e^{-r})$.  A single unsharp $r>0$ fixes $t$
modulo $2\pi/r$, and two values with irrational ratio fix $t$ in the noiseless
model.  Unsharpness is essential, by \Cref{cor:sharp}.  Liu and Wu already
compute the qubit form of their product and read $t$ as a physical ``time

An exact noiseless implication from four probabilities; no finite-noise claim.
-/
theorem detection_four_observations (t s r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (hirr : ¬ ∃ q : ℚ, r₁/r₂ = (q : ℝ))
    (h10 : detection t r₁ 0 = detection s r₁ 0)
    (h11 : detection t r₁ (Real.pi/2) = detection s r₁ (Real.pi/2))
    (h20 : detection t r₂ 0 = detection s r₂ 0)
    (h21 : detection t r₂ (Real.pi/2) = detection s r₂ (Real.pi/2)) : t = s := by
  apply PaperA.noiseless_identifiability t s r₁ r₂ h₁ h₂ hirr
  intro φ
  exact ⟨detection_two_quadratures t s r₁ h₁ h10 h11 φ,
    detection_two_quadratures t s r₂ h₂ h20 h21 φ⟩

/-- paper/main.tex:1385-1400 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
\begin{remark}[Composite systems]\label{rem:composition}
Let $A = \Mnsa{n}$, $B = \Mnsa{m}$ with $n, m \geq 2$, and $AB = \Mnsa{nm}$, so
that $AB$ has rank at least four.  Say that the product of $AB$ \emph{restricts
to} that of $A$ if $(a \otimes \id)\cdot(b \otimes \id) = (\seqp{a}{b}) \otimes \id$
for all effects $a, b$ of $A$, and similarly for $B$.  By \Cref{thm:complex}, $AB$
carries $\circ_t$ for one $t$, and
$(a \otimes \id)^{1/2+it}(b \otimes \id)(a \otimes \id)^{1/2-it}
= (a \circ_t b) \otimes \id$.  So if the product of $AB$ restricts to that of
$A$, the product of $A$ is $\circ_t$ with the composite's $t$; if it also restricts
to that of $B$, the same holds for $B$, and $A$, $B$ and $AB$ share one twist.  In
particular a qubit $A = \Mnsa{2}$ that is a restricting factor of one such
composite has a constant frame function (\Cref{cor:qubit-classification}).  For
a family of complex systems in which every pair has a composite restricting to
both factors, all members share one twist.
Fiorentino and Weigert~\cite{FiorentinoWeigert2026} single out the analogous
compatibility of local and global updates as the condition that extends the

Every ordered pair, including i=i, has a standard restricting composite. This covers a singleton qubit without assuming its twist. For distinct-pair-only families one must require at least two members; an unconstrained singleton qubit need not have a constant twist. The empty family admits any t.
-/
-- LATER_PROOF: composition_family
theorem composition_family {I : Type} (V : I → Type)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, EuclideanJordanAlgebra (V i)] [∀ i, FiniteDimensional ℝ (V i)]
    (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (M : ∀ i, ComplexModel (V i) (n i)) (P : ∀ i, SequentialProduct (V i))
    (C : I → I → Type)
    [∀ i j, NormedAddCommGroup (C i j)] [∀ i j, InnerProductSpace ℝ (C i j)]
    [∀ i j, EuclideanJordanAlgebra (C i j)]
    [∀ i j, FiniteDimensional ℝ (C i j)]
    (MC : ∀ i j, ComplexModel (C i j) (n i * n j))
    (PC : ∀ i j, SequentialProduct (C i j))
    (ιA : ∀ i j, V i →ₗ[ℝ] C i j) (ιB : ∀ i j, V j →ₗ[ℝ] C i j)
    (e : ∀ i j, Fin (n i * n j) ≃ Fin (n i) × Fin (n j))
    (hA : ∀ i j a k l, (MC i j).map (ιA i j a) k l =
      (M i).map a ((e i j k).1) ((e i j l).1) *
        (if (e i j k).2 = (e i j l).2 then 1 else 0))
    (hB : ∀ i j b k l, (MC i j).map (ιB i j b) k l =
      (if (e i j k).1 = (e i j l).1 then 1 else 0) *
        (M j).map b ((e i j k).2) ((e i j l).2))
    (hrA : ∀ i j a b, IsEffect a → IsEffect b →
      (PC i j).sp (ιA i j a) (ιA i j b) = ιA i j ((P i).sp a b))
    (hrB : ∀ i j a b, IsEffect a → IsEffect b →
      (PC i j).sp (ιB i j a) (ιB i j b) = ιB i j ((P j).sp a b)) :
    ∃ t : ℝ, (∀ i, Twist (M i) t (P i).sp) ∧
      ∀ i j, Twist (MC i j) t (PC i j).sp := by
  sorry

/-- paper/main.tex:1397-1400 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
a family of complex systems in which every pair has a composite restricting to
both factors, all members share one twist.
Fiorentino and Weigert~\cite{FiorentinoWeigert2026} single out the analogous
compatibility of local and global updates as the condition that extends the

Explicit vacuous empty-family endpoint, without changing any effect type.
-/
theorem composition_empty {I : Type} [IsEmpty I] (V : I → Type)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, EuclideanJordanAlgebra (V i)] [∀ i, FiniteDimensional ℝ (V i)]
    (n : I → ℕ) (M : ∀ i, ComplexModel (V i) (n i))
    (P : ∀ i, SequentialProduct (V i)) : ∃ t : ℝ, ∀ i, Twist (M i) t (P i).sp := by
  exact ⟨0, fun i => isEmptyElim i⟩

/-- paper/main.tex:1408-1414 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
two are due, in greater generality, to van de Wetering and to Gudder and
Latr\'emoli\`ere (\Cref{sec:priorart}).  Write $E(x,y)$ for the action of $\seqp{a}{(\cdot)}$ on a
coherence block $V_{ij}$ when $a$ has eigenvalues $x, y$ on the atoms
$p_i, p_j$; by \Cref{thm:complex} it is
$E(x,y) = \sqrt{xy}\,\exp(t\log(x/y)\,\mathcal{J})$ for $x, y > 0$ and
$E(x,y) = 0$ when $xy = 0$, with $\mathcal{J}$ the block's complex structure.  \emph{Peirce exchange covariance} means
$E(x,y) = E(y,x)$ with $\mathcal{J}$ held fixed.

The ordered i,j slot fixes the complex orientation; exchange never swaps this slot.
-/
def coherence {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  u * coordSlot star i j z * u.conjTranspose

/-- paper/main.tex:1408-1414 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
two are due, in greater generality, to van de Wetering and to Gudder and
Latr\'emoli\`ere (\Cref{sec:priorart}).  Write $E(x,y)$ for the action of $\seqp{a}{(\cdot)}$ on a
coherence block $V_{ij}$ when $a$ has eigenvalues $x, y$ on the atoms
$p_i, p_j$; by \Cref{thm:complex} it is
$E(x,y) = \sqrt{xy}\,\exp(t\log(x/y)\,\mathcal{J})$ for $x, y > 0$ and
$E(x,y) = 0$ when $xy = 0$, with $\mathcal{J}$ the block's complex structure.  \emph{Peirce exchange covariance} means
$E(x,y) = E(y,x)$ with $\mathcal{J}$ held fixed.

Complex coordinates realize the fixed block complex structure as multiplication by i, including the zero branch.
-/
def peirceAction (t x y : ℝ) (z : ℂ) : ℂ :=
  if 0 < x ∧ 0 < y then
    (Real.sqrt (x*y) : ℂ) * Complex.exp (Complex.I * (t*Real.log (x/y))) * z
  else 0

/-- paper/main.tex:1408-1414 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
two are due, in greater generality, to van de Wetering and to Gudder and
Latr\'emoli\`ere (\Cref{sec:priorart}).  Write $E(x,y)$ for the action of $\seqp{a}{(\cdot)}$ on a
coherence block $V_{ij}$ when $a$ has eigenvalues $x, y$ on the atoms
$p_i, p_j$; by \Cref{thm:complex} it is
$E(x,y) = \sqrt{xy}\,\exp(t\log(x/y)\,\mathcal{J})$ for $x, y > 0$ and
$E(x,y) = 0$ when $xy = 0$, with $\mathcal{J}$ the block's complex structure.  \emph{Peirce exchange covariance} means
$E(x,y) = E(y,x)$ with $\mathcal{J}$ held fixed.

Equality of the actual positive linear extensions on each coherence block. Swapping eigenvalues keeps u, i,j and z fixed; zero eigenvalues are included. The second input can be any block vector, via the existing leftMap extension.
-/
def PeirceExchange {n : ℕ} (M : ComplexModel J n) (P : SequentialProduct J) : Prop :=
  ∀ (u : Matrix (Fin n) (Fin n) ℂ), u*u.conjTranspose = 1 → u.conjTranspose*u = 1 →
  ∀ i j : Fin n, i ≠ j → ∀ lam : Fin n → ℝ, (∀ k, lam k ∈ Set.Icc 0 1) →
  ∀ a a' b : J, IsEffect a → IsEffect a' →
    M.map a = u * Matrix.diagonal (fun k => (lam k : ℂ)) * u.conjTranspose →
    M.map a' = u * Matrix.diagonal (fun k => (lam (Equiv.swap i j k) : ℂ)) *
      u.conjTranspose →
    (∃ z : ℂ, M.map b = coherence u i j z) →
    leftMap P a b = leftMap P a' b

/-- paper/main.tex:1408-1414 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
two are due, in greater generality, to van de Wetering and to Gudder and
Latr\'emoli\`ere (\Cref{sec:priorart}).  Write $E(x,y)$ for the action of $\seqp{a}{(\cdot)}$ on a
coherence block $V_{ij}$ when $a$ has eigenvalues $x, y$ on the atoms
$p_i, p_j$; by \Cref{thm:complex} it is
$E(x,y) = \sqrt{xy}\,\exp(t\log(x/y)\,\mathcal{J})$ for $x, y > 0$ and
$E(x,y) = 0$ when $xy = 0$, with $\mathcal{J}$ the block's complex structure.  \emph{Peirce exchange covariance} means
$E(x,y) = E(y,x)$ with $\mathcal{J}$ held fixed.

The zero and singular branches have zero block action.
-/
-- LATER_PROOF: peirceAction_zero
theorem peirceAction_zero (t x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x*y = 0)
    (z : ℂ) : peirceAction t x y z = 0 := by
  have hnot : ¬ (0 < x ∧ 0 < y) := by
    intro h
    have hpos : 0 < x * y := mul_pos h.1 h.2
    linarith
  simp [peirceAction, hnot]

/-- paper/main.tex:1408-1414 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
two are due, in greater generality, to van de Wetering and to Gudder and
Latr\'emoli\`ere (\Cref{sec:priorart}).  Write $E(x,y)$ for the action of $\seqp{a}{(\cdot)}$ on a
coherence block $V_{ij}$ when $a$ has eigenvalues $x, y$ on the atoms
$p_i, p_j$; by \Cref{thm:complex} it is
$E(x,y) = \sqrt{xy}\,\exp(t\log(x/y)\,\mathcal{J})$ for $x, y > 0$ and
$E(x,y) = 0$ when $xy = 0$, with $\mathcal{J}$ the block's complex structure.  \emph{Peirce exchange covariance} means
$E(x,y) = E(y,x)$ with $\mathcal{J}$ held fixed.

Bridge from the actual product extension to E on each fixed oriented block, with all boundary eigenvalues.
-/
-- LATER_PROOF: peirce_action_formula
theorem peirce_action_formula {n : ℕ} (M : ComplexModel J n) (P : SequentialProduct J)
    (t : ℝ) (ht : Twist M t P.sp)
    (u : Matrix (Fin n) (Fin n) ℂ) (hu : u*u.conjTranspose = 1)
    (hu' : u.conjTranspose*u = 1) (i j : Fin n) (hij : i ≠ j)
    (lam : Fin n → ℝ) (hlam : ∀ k, lam k ∈ Set.Icc 0 1)
    (a b : J) (ha : IsEffect a)
    (hmap : M.map a = u * Matrix.diagonal (fun k => (lam k : ℂ)) * u.conjTranspose)
    (z : ℂ) (hb : M.map b = coherence u i j z) :
    M.map (leftMap P a b) = coherence u i j (peirceAction t (lam i) (lam j) z) := by
  sorry

/-- paper/main.tex:1408-1414 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
two are due, in greater generality, to van de Wetering and to Gudder and
Latr\'emoli\`ere (\Cref{sec:priorart}).  Write $E(x,y)$ for the action of $\seqp{a}{(\cdot)}$ on a
coherence block $V_{ij}$ when $a$ has eigenvalues $x, y$ on the atoms
$p_i, p_j$; by \Cref{thm:complex} it is
$E(x,y) = \sqrt{xy}\,\exp(t\log(x/y)\,\mathcal{J})$ for $x, y > 0$ and
$E(x,y) = 0$ when $xy = 0$, with $\mathcal{J}$ the block's complex structure.  \emph{Peirce exchange covariance} means
$E(x,y) = E(y,x)$ with $\mathcal{J}$ held fixed.

The scalar identity is a conclusion/bridge, never the definition of product exchange.
-/
-- LATER_PROOF: peirce_exchange_character
theorem peirce_exchange_character {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n)
    (P : SequentialProduct J) (t : ℝ) (ht : Twist M t P.sp) :
    PeirceExchange M P ↔
      ∀ x y : ℝ, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 →
      Complex.exp (Complex.I*(t*Real.log (x/y))) =
        Complex.exp (Complex.I*(t*Real.log (y/x))) := by
  sorry

/-- paper/main.tex:1416-1423 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
\begin{corollary}[Selectors that fix $t = 0$]\label{cor:selectors}
On $\Mnsa{n}$, $n \geq 3$, a sequential product is the L\"uders product if any
of the following holds: (i)~Peirce exchange covariance on every coherence
block; (ii)~trace-form symmetry,
$\langle \seqp{a}{b}, c\rangle = \langle b, \seqp{a}{c}\rangle$;
(iii)~covariance under every unital order automorphism (the transpose
suffices).
\end{corollary}

Operational exchange selects the Luders product on the complete effect domain.
-/
-- LATER_PROOF: selectors_peirce_exchange
theorem selectors_peirce_exchange {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n)
    (P : SequentialProduct J) (hs : PeirceExchange M P) : Rigid P := by
  sorry

/-- paper/main.tex:1416-1423 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
\begin{corollary}[Selectors that fix $t = 0$]\label{cor:selectors}
On $\Mnsa{n}$, $n \geq 3$, a sequential product is the L\"uders product if any
of the following holds: (i)~Peirce exchange covariance on every coherence
block; (ii)~trace-form symmetry,
$\langle \seqp{a}{b}, c\rangle = \langle b, \seqp{a}{c}\rangle$;
(iii)~covariance under every unital order automorphism (the transpose
suffices).
\end{corollary}

Canonical Jordan trace pairing on the chosen complex matrix model, not the arbitrary ambient associative inner product. The existing PaperA.selectors_trace is retain-only.
-/
def canonicalTraceForm {n : ℕ} (M : ComplexModel J n) (a b : J) : ℝ :=
  (Matrix.trace (M.map a * M.map b)).re

/-- paper/main.tex:1416-1423 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
\begin{corollary}[Selectors that fix $t = 0$]\label{cor:selectors}
On $\Mnsa{n}$, $n \geq 3$, a sequential product is the L\"uders product if any
of the following holds: (i)~Peirce exchange covariance on every coherence
block; (ii)~trace-form symmetry,
$\langle \seqp{a}{b}, c\rangle = \langle b, \seqp{a}{c}\rangle$;
(iii)~covariance under every unital order automorphism (the transpose
suffices).
\end{corollary}

Unital square-cone order automorphisms act on the actual effect product.
-/
def OrderCovariant (P : SequentialProduct J) : Prop :=
  ∀ g : J ≃ₗ[ℝ] J, g 1 = 1 → (∀ x, Positive (g x) ↔ Positive x) →
    ∀ a b, IsEffect a → IsEffect b → P.sp (g a) (g b) = g (P.sp a b)

/-- paper/main.tex:1416-1423 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
\begin{corollary}[Selectors that fix $t = 0$]\label{cor:selectors}
On $\Mnsa{n}$, $n \geq 3$, a sequential product is the L\"uders product if any
of the following holds: (i)~Peirce exchange covariance on every coherence
block; (ii)~trace-form symmetry,
$\langle \seqp{a}{b}, c\rangle = \langle b, \seqp{a}{c}\rangle$;
(iii)~covariance under every unital order automorphism (the transpose
suffices).
\end{corollary}

Full unital order covariance implies the existing transpose selector.
-/
-- LATER_PROOF: selectors_order_covariant
theorem selectors_order_covariant {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n)
    (P : SequentialProduct J) (hs : OrderCovariant P) : Rigid P := by
  sorry

/-- paper/main.tex:1426-1431 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
(i) $E(x,y) = E(y,x)$ for all $x, y$ iff $t = 0$.  (ii) Peirce spaces are
trace-orthogonal, so symmetry is self-adjointness of each block rotation
$\exp(t\log(x/y)\,\mathcal{J})$; a real plane rotation is self-adjoint only at
angles in $\pi\mathbb{Z}$, but $t\log(x/y)$ ranges over an interval, so $t = 0$.
(iii) The transpose acts on each block by $\mathcal{J} \mapsto -\mathcal{J}$,
forcing $t = -t$.

Transpose reverses the fixed complex orientation z ↦ conjugate z.
-/
-- LATER_PROOF: transpose_orientation
theorem transpose_orientation {n : ℕ} (i j : Fin n) (hij : i ≠ j) (z : ℂ) :
    (coordSlot star i j z).transpose = coordSlot star i j (star z) := by
  ext a b
  simp only [Matrix.transpose_apply, coordSlot]
  split_ifs <;> simp_all

/-- paper/main.tex:1416-1423 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
\begin{corollary}[Selectors that fix $t = 0$]\label{cor:selectors}
On $\Mnsa{n}$, $n \geq 3$, a sequential product is the L\"uders product if any
of the following holds: (i)~Peirce exchange covariance on every coherence
block; (ii)~trace-form symmetry,
$\langle \seqp{a}{b}, c\rangle = \langle b, \seqp{a}{c}\rangle$;
(iii)~covariance under every unital order automorphism (the transpose
suffices).
\end{corollary}

All three clauses at their printed rank/domain, using the retained trace and transpose endpoints.
-/
theorem operational_selectors {n : ℕ} (M : ComplexModel J n) (hn : 3 ≤ n) (P : SequentialProduct J)
    (hs : PeirceExchange M P ∨
      (∀ a b c, IsEffect a → IsEffect b → IsEffect c →
        canonicalTraceForm M (P.sp a b) c = canonicalTraceForm M b (P.sp a c)) ∨
      (∀ a b aT bT, IsEffect a → IsEffect b → IsEffect aT → IsEffect bT →
        M.map aT = (M.map a).transpose → M.map bT = (M.map b).transpose →
        M.map (P.sp aT bT) = (M.map (P.sp a b)).transpose)) : Rigid P := by
  rcases hs with h | h | h
  · exact selectors_peirce_exchange M hn P h
  · exact PaperA.selectors_trace M hn P h
  · exact PaperA.selectors_transpose M hn P h

/-- paper/main.tex:1385-1400 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
\begin{remark}[Composite systems]\label{rem:composition}
Let $A = \Mnsa{n}$, $B = \Mnsa{m}$ with $n, m \geq 2$, and $AB = \Mnsa{nm}$, so
that $AB$ has rank at least four.  Say that the product of $AB$ \emph{restricts
to} that of $A$ if $(a \otimes \id)\cdot(b \otimes \id) = (\seqp{a}{b}) \otimes \id$
for all effects $a, b$ of $A$, and similarly for $B$.  By \Cref{thm:complex}, $AB$
carries $\circ_t$ for one $t$, and
$(a \otimes \id)^{1/2+it}(b \otimes \id)(a \otimes \id)^{1/2-it}
= (a \circ_t b) \otimes \id$.  So if the product of $AB$ restricts to that of
$A$, the product of $A$ is $\circ_t$ with the composite's $t$; if it also restricts
to that of $B$, the same holds for $B$, and $A$, $B$ and $AB$ share one twist.  In
particular a qubit $A = \Mnsa{2}$ that is a restricting factor of one such
composite has a constant frame function (\Cref{cor:qubit-classification}).  For
a family of complex systems in which every pair has a composite restricting to
both factors, all members share one twist.
Fiorentino and Weigert~\cite{FiorentinoWeigert2026} single out the analogous
compatibility of local and global updates as the condition that extends the

For a family with at least two members, only distinct pairs need restricting composites. Empty families are treated by composition_empty. A singleton qubit requires a restricting self-composite as in composition_family; no unconditional constant-t singleton claim is made.
-/
-- LATER_PROOF: composition_family_distinct
theorem composition_family_distinct {I : Type} [Nontrivial I] (V : I → Type)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, EuclideanJordanAlgebra (V i)] [∀ i, FiniteDimensional ℝ (V i)]
    (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (M : ∀ i, ComplexModel (V i) (n i)) (P : ∀ i, SequentialProduct (V i))
    (C : I → I → Type)
    [∀ i j, NormedAddCommGroup (C i j)] [∀ i j, InnerProductSpace ℝ (C i j)]
    [∀ i j, EuclideanJordanAlgebra (C i j)]
    [∀ i j, FiniteDimensional ℝ (C i j)]
    (MC : ∀ i j, ComplexModel (C i j) (n i * n j))
    (PC : ∀ i j, SequentialProduct (C i j))
    (ιA : ∀ i j, V i →ₗ[ℝ] C i j) (ιB : ∀ i j, V j →ₗ[ℝ] C i j)
    (e : ∀ i j, Fin (n i * n j) ≃ Fin (n i) × Fin (n j))
    (hA : ∀ i j, i ≠ j → ∀ a k l, (MC i j).map (ιA i j a) k l =
      (M i).map a ((e i j k).1) ((e i j l).1) *
        (if (e i j k).2 = (e i j l).2 then 1 else 0))
    (hB : ∀ i j, i ≠ j → ∀ b k l, (MC i j).map (ιB i j b) k l =
      (if (e i j k).1 = (e i j l).1 then 1 else 0) *
        (M j).map b ((e i j k).2) ((e i j l).2))
    (hrA : ∀ i j, i ≠ j → ∀ a b, IsEffect a → IsEffect b →
      (PC i j).sp (ιA i j a) (ιA i j b) = ιA i j ((P i).sp a b))
    (hrB : ∀ i j, i ≠ j → ∀ a b, IsEffect a → IsEffect b →
      (PC i j).sp (ιB i j a) (ιB i j b) = ιB i j ((P j).sp a b)) :
    ∃ t : ℝ, (∀ i, Twist (M i) t (P i).sp) ∧
      ∀ i j, i ≠ j → Twist (MC i j) t (PC i j).sp := by
  sorry

/-- paper/main.tex:1385-1400 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33:
\begin{remark}[Composite systems]\label{rem:composition}
Let $A = \Mnsa{n}$, $B = \Mnsa{m}$ with $n, m \geq 2$, and $AB = \Mnsa{nm}$, so
that $AB$ has rank at least four.  Say that the product of $AB$ \emph{restricts
to} that of $A$ if $(a \otimes \id)\cdot(b \otimes \id) = (\seqp{a}{b}) \otimes \id$
for all effects $a, b$ of $A$, and similarly for $B$.  By \Cref{thm:complex}, $AB$
carries $\circ_t$ for one $t$, and
$(a \otimes \id)^{1/2+it}(b \otimes \id)(a \otimes \id)^{1/2-it}
= (a \circ_t b) \otimes \id$.  So if the product of $AB$ restricts to that of
$A$, the product of $A$ is $\circ_t$ with the composite's $t$; if it also restricts
to that of $B$, the same holds for $B$, and $A$, $B$ and $AB$ share one twist.  In
particular a qubit $A = \Mnsa{2}$ that is a restricting factor of one such
composite has a constant frame function (\Cref{cor:qubit-classification}).  For
a family of complex systems in which every pair has a composite restricting to
both factors, all members share one twist.
Fiorentino and Weigert~\cite{FiorentinoWeigert2026} single out the analogous
compatibility of local and global updates as the condition that extends the

A singleton system has a constant twist when it admits a restricting self-composite. The condition is necessary for this formulation at rank two; it is not inferred from the vacuous distinct-pair premise.
-/
theorem composition_singleton {L : Type}
    [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    [EuclideanJordanAlgebra L] [FiniteDimensional ℝ L]
    {n : ℕ} (hn : 2 ≤ n) (M : ComplexModel J n)
    (MC : ComplexModel L (n*n)) (P : SequentialProduct J) (PC : SequentialProduct L)
    (ιA ιB : J →ₗ[ℝ] L) (e : Fin (n*n) ≃ Fin n × Fin n)
    (hA : ∀ a i j, MC.map (ιA a) i j = M.map a (e i).1 (e j).1 *
      (if (e i).2 = (e j).2 then 1 else 0))
    (hB : ∀ b i j, MC.map (ιB b) i j =
      (if (e i).1 = (e j).1 then 1 else 0) * M.map b (e i).2 (e j).2)
    (hrA : ∀ a b, IsEffect a → IsEffect b → PC.sp (ιA a) (ιA b) = ιA (P.sp a b))
    (hrB : ∀ a b, IsEffect a → IsEffect b → PC.sp (ιB a) (ιB b) = ιB (P.sp a b)) :
    ∃ t : ℝ, Twist M t P.sp := by
  obtain ⟨t, _, ht, _⟩ := PaperA.composition hn hn M M MC P P PC ιA ιB e hA hB hrA hrB
  exact ⟨t, ht⟩

end PaperA.Spec.Observations

import PaperA.Claims

/-! Interfaces for the necessity argument of the spin classification.
The original theorem statements are retained in PaperA.Claims. New theorem
bodies marked LATER_PROOF are additional proof obligations, not closures. -/
noncomputable section
open EuclideanJordan
namespace PaperA.Spec.SpinNecessity

variable {J : Type} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J]

/-- A concrete normalization; no choice of a positive-cone extension is assumed. -/
def normalization (x : J) : ℝ := max 1 (ouNorm x)

/-- Extend using the normalization. Independence of this choice is a theorem below. -/
def coneLeft (P : SequentialProduct J) (x : J) : J →L[ℝ] J :=
  normalization x • leftMap P ((normalization x)⁻¹ • x)

/-- Comparison on the interior of the cone, using the original Jordan Q. -/
def coneTheta (P : SequentialProduct J) (x y : J) : J :=
  Q (inverseSqrt x) (coneLeft P x y)

/-- Diagonal data in a fixed spin frame; eigenvalues need not be ordered. -/
def frameElement {d : ℕ} (M : SpinModel J d) (v : Vec d) (lp lm : ℝ) : J :=
  M.equiv.symm (lp • spinAtom v + lm • spinAtom (-v))

/-- The scalar-normalized exponential path through μe. -/
def framePath {d : ℕ} (M : SpinModel J d) (v : Vec d) (μ t : ℝ) : J :=
  frameElement M v (μ * Real.exp (t/2)) (μ * Real.exp (-t/2))

/-- Tangent hyperplane, with its inherited Euclidean structure. -/
def tangent {d : ℕ} (v : Vec d) : Submodule ℝ (Vec d) :=
  (Submodule.span ℝ {v})ᗮ

/-- Algebraic and exponential characterization of a generator at one axis.
There is no continuity or oddness hypothesis on the axis parameter. -/
def IsGenerator {d : ℕ} (P : SequentialProduct J) (M : SpinModel J d)
    (v : Vec d) (B : Vec d →L[ℝ] Vec d) : Prop :=
  (∀ x y, inner ℝ x (B y) = -inner ℝ (B x) y) ∧ B v = 0 ∧
  ∀ lp lm : ℝ, 0 < lp → 0 < lm → ∀ y : J,
    M.equiv (coneTheta P (frameElement M v lp lm) y) =
      ((M.equiv y).1, NormedSpace.exp (Real.log (lp/lm) • B) (M.equiv y).2)

/-- The branch domain of the principal logarithm, in ambient operators. -/
def logDomain (d : ℕ) : Set (Vec d →L[ℝ] Vec d) :=
  {R | ∃ B : Vec d →L[ℝ] Vec d,
    (∀ x y, inner ℝ x (B y) = -inner ℝ (B x) y) ∧
    ‖B‖ < Real.pi ∧ NormedSpace.exp B = R}

/-- prose:spin_positive_extension; paper/main.tex:1069-1074 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33.
Verbatim frozen text:
of the cone: for $x > 0$ put $L_x := s\,L_{x/s}$ for any $s \geq \|x\|_e$, which
is independent of $s$ by \Cref{lem:scalars}, and put
$\Theta_x := Q_{x^{-1/2}}L_x$.  Then $L_{cx} = cL_x$ and $\Theta_{cx} = \Theta_x$
for $c > 0$, and on invertible effects $\Theta_x$ is the comparison
automorphism of \Cref{prop:theta}.

The statement below records this step as additional proof debt.
-/
-- LATER_PROOF: positive_extension
theorem positive_extension (P : SequentialProduct J) (x : J) (hx : StrictPositive x) :
    (∀ s : ℝ, 0 < s → ouNorm x ≤ s →
      IsEffect (s⁻¹ • x) ∧ StrictPositive (s⁻¹ • x) ∧
      coneLeft P x = s • leftMap P (s⁻¹ • x)) ∧
    (∀ c : ℝ, 0 < c → coneLeft P (c • x) = c • coneLeft P x ∧
      ∀ y, coneTheta P (c • x) y = coneTheta P x y) ∧
    (IsEffect x → coneLeft P x = leftMap P x ∧
      ∀ y, coneTheta P x y = theta P x y) ∧
    ∃ g : J ≃ₗ[ℝ] J, JordanAuto g ∧ ∀ y, g y = coneTheta P x y := by
  sorry

/-- prose:spin_frame_generator; paper/main.tex:1076-1092 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33.
Verbatim frozen text:
Normalizing to an invertible effect, \Cref{prop:theta} and its fixing clause
make $\Theta_x$ a Jordan automorphism fixing $p_v$ and $p_{-v}$.  So
$\Theta_x = 1 \oplus O_x$ with $O_x \in \mathrm{O}(d)$ and $O_xv = v$
(\Cref{sec:spin-def}).  For $x, x'$ positive and diagonal in the frame
$\{p_v, p_{-v}\}$, normalizing each into the effects and using
\Cref{prop:theta}(iii) with scale invariance gives
$\Theta_{x \circ x'} = \Theta_x\Theta_{x'}$.  Also $\Theta_{ce} = I$ by
\Cref{lem:scalars}.  Since
$x = \sqrt{\lambda_+\lambda_-}\,(e^{\ell/2}p_v + e^{-\ell/2}p_{-v})$ with
$\ell = \log(\lambda_+/\lambda_-)$, $\Theta_x$ depends only on $(v, \ell)$, and
$\ell \mapsto O_{v}(\ell) := O_{x}|_{v^\perp}$ is a continuous homomorphism
$(\mathbb{R}, +) \to \mathrm{SO}(v^\perp)$, continuity coming from
\Cref{prop:theta}(ii).  By the theorem on continuous one-parameter matrix
groups~\cite[Ch.~2]{Hall2015} there is a unique skew $A(v)$ on $v^\perp$ with
$O_v(\ell) = \exp(\ell A(v))$.  Extend $A(v)$ by $A(v)v = 0$.

\emph{Step 2: oddness.}  The same $x$ has frame data $(-v, -\ell)$ in the reversed
The statement below records this step as additional proof debt.
-/
-- LATER_PROOF: frame_generator
theorem frame_generator (P : SequentialProduct J) {d : ℕ} (M : SpinModel J d)
    (hd : 2 ≤ d) (v : Vec d) (hv : ‖v‖ = 1) :
    ∃ B : Vec d →L[ℝ] Vec d, IsGenerator P M v B ∧
      (∀ C, IsGenerator P M v C → C = B) ∧
      ∃ O : ℝ → (Vec d →L[ℝ] Vec d), Continuous O ∧
        O 0 = ContinuousLinearMap.id ℝ (Vec d) ∧
        (∀ s t, O (s+t) = (O s).comp (O t)) ∧
        (∀ t, O t = NormedSpace.exp (t • B)) ∧
        (∀ t, O t v = v) ∧
        (∀ t, ∃ R : tangent v ≃ₗᵢ[ℝ] tangent v,
          LinearMap.det R.toLinearEquiv.toLinearMap = 1 ∧
          ∀ w : tangent v, (R w).val = O t w.val) := by
  sorry

/-- prose:spin_oddness; paper/main.tex:1094-1096 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33.
Verbatim frozen text:
uniqueness of the generator gives $A(-v) = -A(v)$.

\emph{Step 3: boundedness.}  Suppose $\|A(v_j)\| \to \infty$ in the Euclidean
The statement below records this step as additional proof debt.
-/
-- LATER_PROOF: reversal_uniqueness
theorem reversal_uniqueness (P : SequentialProduct J) {d : ℕ} (M : SpinModel J d)
    (hd : 2 ≤ d) (v : Vec d) (hv : ‖v‖ = 1)
    (B C : Vec d →L[ℝ] Vec d) (hB : IsGenerator P M v B)
    (hC : IsGenerator P M (-v) C) : C = -B := by
  sorry

/-- prose:spin_necessity_bound; paper/main.tex:1098-1105 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33.
Verbatim frozen text:
$a_j = \mu(e^{s_j/2}p_{v_j} + e^{-s_j/2}p_{-v_j})$.  Eventually these are
invertible effects, and $a_j \to \mu e$ whatever the $v_j$.  On a
maximal-frequency rotation plane of $A(v_j)$, $\exp(s_jA(v_j))$ acts as $-I$,
so $\|\Theta_{a_j} - I\| \geq 2$, contradicting continuity of $\Theta$ at
$\mu e$, where $\Theta_{\mu e} = I$.  Hence $M := \sup_v\|A(v)\| < \infty$.

\emph{Step 4: continuity.}  If $M = 0$ there is nothing to prove.  Otherwise
fix $s > 0$ with $sM < \pi$ and $\mu e^{s/2} < 1$.  Then
The statement below records this step as additional proof debt.
-/
-- LATER_PROOF: scalar_approach
theorem scalar_approach {d : ℕ} (M : SpinModel J d) (hd : 2 ≤ d)
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ < 1)
    (v : ℕ → sphere d) (t : ℕ → ℝ) (ht : Filter.Tendsto t Filter.atTop (nhds 0)) :
    (∀ᶠ j in Filter.atTop, IsEffect (framePath M (v j).val μ (t j)) ∧
      StrictPositive (framePath M (v j).val μ (t j))) ∧
    Filter.Tendsto (fun j => ouNorm (framePath M (v j).val μ (t j) - μ • (1 : J)))
      Filter.atTop (nhds 0) := by
  sorry

/-- prose:spin_necessity_bound; paper/main.tex:1098-1105 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33.
Verbatim frozen text:
$a_j = \mu(e^{s_j/2}p_{v_j} + e^{-s_j/2}p_{-v_j})$.  Eventually these are
invertible effects, and $a_j \to \mu e$ whatever the $v_j$.  On a
maximal-frequency rotation plane of $A(v_j)$, $\exp(s_jA(v_j))$ acts as $-I$,
so $\|\Theta_{a_j} - I\| \geq 2$, contradicting continuity of $\Theta$ at
$\mu e$, where $\Theta_{\mu e} = I$.  Hence $M := \sup_v\|A(v)\| < \infty$.

\emph{Step 4: continuity.}  If $M = 0$ there is nothing to prove.  Otherwise
fix $s > 0$ with $sM < \pi$ and $\mu e^{s/2} < 1$.  Then
The statement below records this step as additional proof debt.
-/
-- LATER_PROOF: product_uniform_small
theorem product_uniform_small (P : SequentialProduct J) {d : ℕ} (M : SpinModel J d)
    (hd : 2 ≤ d) (A : sphere d → (Vec d →L[ℝ] Vec d))
    (hA : ∀ v, IsGenerator P M v.val (A v))
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v t, |t| < δ →
      IsEffect (framePath M v.val μ t) ∧ StrictPositive (framePath M v.val μ t) ∧
      ‖NormedSpace.exp (t • A v) - ContinuousLinearMap.id ℝ (Vec d)‖ < ε := by
  sorry

/-- prose:spin_necessity_bound; paper/main.tex:1098-1105 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33.
Verbatim frozen text:
$a_j = \mu(e^{s_j/2}p_{v_j} + e^{-s_j/2}p_{-v_j})$.  Eventually these are
invertible effects, and $a_j \to \mu e$ whatever the $v_j$.  On a
maximal-frequency rotation plane of $A(v_j)$, $\exp(s_jA(v_j))$ acts as $-I$,
so $\|\Theta_{a_j} - I\| \geq 2$, contradicting continuity of $\Theta$ at
$\mu e$, where $\Theta_{\mu e} = I$.  Hence $M := \sup_v\|A(v)\| < \infty$.

\emph{Step 4: continuity.}  If $M = 0$ there is nothing to prove.  Otherwise
fix $s > 0$ with $sM < \pi$ and $\mu e^{s/2} < 1$.  Then
The statement below records this step as additional proof debt.
-/
-- LATER_PROOF: maximal_frequency
theorem maximal_frequency {d : ℕ} (B : Vec d →L[ℝ] Vec d)
    (hB : ∀ x y, inner ℝ x (B y) = -inner ℝ (B x) y) (hne : B ≠ 0) :
    ∃ u w : Vec d, ‖u‖ = 1 ∧ ‖w‖ = 1 ∧ inner ℝ u w = 0 ∧
      B u = ‖B‖ • w ∧ B w = -‖B‖ • u ∧
      NormedSpace.exp ((Real.pi / ‖B‖) • B) u = -u ∧
      2 ≤ ‖NormedSpace.exp ((Real.pi / ‖B‖) • B) - ContinuousLinearMap.id ℝ (Vec d)‖ := by
  sorry

/-- prose:spin_necessity_bound; paper/main.tex:1098-1105 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33.
Verbatim frozen text:
$a_j = \mu(e^{s_j/2}p_{v_j} + e^{-s_j/2}p_{-v_j})$.  Eventually these are
invertible effects, and $a_j \to \mu e$ whatever the $v_j$.  On a
maximal-frequency rotation plane of $A(v_j)$, $\exp(s_jA(v_j))$ acts as $-I$,
so $\|\Theta_{a_j} - I\| \geq 2$, contradicting continuity of $\Theta$ at
$\mu e$, where $\Theta_{\mu e} = I$.  Hence $M := \sup_v\|A(v)\| < \infty$.

\emph{Step 4: continuity.}  If $M = 0$ there is nothing to prove.  Otherwise
fix $s > 0$ with $sM < \pi$ and $\mu e^{s/2} < 1$.  Then
-/
theorem product_generator_bound (P : SequentialProduct J) {d : ℕ} (M : SpinModel J d)
    (hd : 2 ≤ d) (A : sphere d → (Vec d →L[ℝ] Vec d))
    (hA : ∀ v, IsGenerator P M v.val (A v))
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ < 1) : ∃ K : ℝ, ∀ v, ‖A v‖ ≤ K := by
  apply PaperA.spin_generator_bound A (fun v => (hA v).1)
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := product_uniform_small P M hd A hA μ hμ hμ1 ε hε
  exact ⟨δ, hδ, fun v t ht => (h v t ht).2.2⟩

/-- prose:spin_log_continuity; paper/main.tex:1107-1114 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33.
Verbatim frozen text:
spatial part $\exp(sA(v))$ has all rotation angles in $(-\pi, \pi)$.  On that
set the principal matrix logarithm is continuous and inverts $\exp$ on skew
matrices, so $A(v) = s^{-1}\operatorname{Log}\exp(sA(v))$ is continuous.  No
continuous choice of basis of $v^\perp$ is needed.  So $A \in \cA_d$.

\emph{Step 5: the product is $\star_A$.}  For invertible nonscalar $a$,
$L_a = Q_{\sqrt a}\Theta_a = L^A_a$ by Step~1.  For scalar $a = \mu e$,
$L_a = \mu I$ by \Cref{lem:scalars}.  For singular nonscalar $a = \lambda p_v$,
The statement below records this step as additional proof debt.
-/
-- LATER_PROOF: principal_log_reconstruction
theorem principal_log_reconstruction (P : SequentialProduct J) {d : ℕ} (M : SpinModel J d)
    (hd : 2 ≤ d) (A : sphere d → (Vec d →L[ℝ] Vec d))
    (hA : ∀ v, IsGenerator P M v.val (A v))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ v, ‖A v‖ ≤ K)
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ < 1) :
    (K = 0 → ∀ v, A v = 0) ∧ Continuous A ∧
    (0 < K → ∃ s : ℝ, 0 < s ∧ s*K < Real.pi ∧ μ * Real.exp (s/2) < 1) ∧
    ∀ s : ℝ, 0 < s → s*K < Real.pi → μ * Real.exp (s/2) < 1 →
      ∃ Log : (Vec d →L[ℝ] Vec d) → (Vec d →L[ℝ] Vec d),
        ContinuousOn Log (logDomain d) ∧
        (∀ B : Vec d →L[ℝ] Vec d,
          (∀ x y, inner ℝ x (B y) = -inner ℝ (B x) y) →
          ‖B‖ < Real.pi → Log (NormedSpace.exp B) = B) ∧
        Continuous (fun v => NormedSpace.exp (s • A v)) ∧
        (∀ v, ‖s • A v‖ < Real.pi ∧
          A v = s⁻¹ • Log (NormedSpace.exp (s • A v))) := by
  sorry

/-- prose:spin_necessity_boundary; paper/main.tex:1116-1121 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33.
Verbatim frozen text:
$0 < \varepsilon < \lambda$.  Then
$L_{a_\varepsilon} = Q_{\sqrt{a_\varepsilon}}(1 \oplus \exp(\log(\lambda/\varepsilon)A(v)))$
has multipliers $\lambda$, $\varepsilon$ and
$\sqrt{\lambda\varepsilon}\exp(\cdots)$ on $\mathbb{R}p_v$, $\mathbb{R}p_{-v}$ and
$v^\perp$.  The rotation is orthogonal, hence bounded, so \ref{ax:S2} gives
$L_a = \lim_{\varepsilon \to 0}L_{a_\varepsilon} = \lambda Q_{p_v} = Q_{\sqrt a}$.
The statement below records this step as additional proof debt.
-/
-- LATER_PROOF: singular_multipliers
theorem singular_multipliers (P : SequentialProduct J) {d : ℕ} (M : SpinModel J d)
    (hd : 2 ≤ d) (A : sphere d → (Vec d →L[ℝ] Vec d))
    (hA : ∀ v, IsGenerator P M v.val (A v)) (v : sphere d)
    (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    (∀ ε : ℝ, 0 < ε → ε < lam →
      let a := frameElement M v.val lam ε
      IsEffect a ∧ StrictPositive a ∧
      leftMap P a (M.equiv.symm (spinAtom v.val)) =
        lam • M.equiv.symm (spinAtom v.val) ∧
      leftMap P a (M.equiv.symm (spinAtom (-v.val))) =
        ε • M.equiv.symm (spinAtom (-v.val)) ∧
      ∀ y : Vec d, inner ℝ v.val y = 0 →
        M.equiv (leftMap P a (M.equiv.symm (0,y))) =
          (0, Real.sqrt (lam*ε) • NormedSpace.exp (Real.log (lam/ε) • A v) y)) ∧
    (∀ ε : ℝ, 0 < ε → ε < lam →
      ‖Real.sqrt (lam*ε) • NormedSpace.exp (Real.log (lam/ε) • A v)‖ ≤ Real.sqrt (lam*ε)) ∧
    Filter.Tendsto (fun ε : ℝ =>
      Real.sqrt (lam*ε) • NormedSpace.exp (Real.log (lam/ε) • A v))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∀ y : J, Filter.Tendsto (fun ε : ℝ => leftMap P (frameElement M v.val lam ε) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (leftMap P (M.equiv.symm (lam • spinAtom v.val)) y))) ∧
    (∀ y : J, leftMap P (M.equiv.symm (lam • spinAtom v.val)) y =
      lam • Q (M.equiv.symm (spinAtom v.val)) y ∧
      leftMap P (M.equiv.symm (lam • spinAtom v.val)) y =
        Q (sqrt (M.equiv.symm (lam • spinAtom v.val))) y) := by
  sorry

/-- prose:spin_necessity_boundary; paper/main.tex:1116-1121 at 8f389ac87f52df9d28572dbef994d9f03bb9bb33.
Verbatim frozen text:
$0 < \varepsilon < \lambda$.  Then
$L_{a_\varepsilon} = Q_{\sqrt{a_\varepsilon}}(1 \oplus \exp(\log(\lambda/\varepsilon)A(v)))$
has multipliers $\lambda$, $\varepsilon$ and
$\sqrt{\lambda\varepsilon}\exp(\cdots)$ on $\mathbb{R}p_v$, $\mathbb{R}p_{-v}$ and
$v^\perp$.  The rotation is orthogonal, hence bounded, so \ref{ax:S2} gives
$L_a = \lim_{\varepsilon \to 0}L_{a_\varepsilon} = \lambda Q_{p_v} = Q_{\sqrt a}$.
The statement below records this step as additional proof debt.
-/
-- LATER_PROOF: boundary_agreement
theorem boundary_agreement (P : SequentialProduct J) {d : ℕ} (M : SpinModel J d)
    (hd : 2 ≤ d) (A : AxisField d)
    (hA : ∀ v : sphere d, IsGenerator P M v.val (A.A v.val)) :
    (∀ μ : ℝ, μ ∈ Set.Icc 0 1 → leftMap P (μ • (1 : J)) =
      μ • ContinuousLinearMap.id ℝ J) ∧
    leftMap P (0 : J) = 0 ∧
    (∀ b : J, IsEffect b → P.sp 0 b = 0) ∧
    (∀ v : sphere d, ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ b : J, IsEffect b →
      P.sp (M.equiv.symm (lam • spinAtom v.val)) b =
        Q (sqrt (M.equiv.symm (lam • spinAtom v.val))) b) ∧
    Agrees P.sp (spinOn M A) := by
  sorry

end PaperA.Spec.SpinNecessity

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Rational-clock classification: compiled proposition interface

This file defines the proposition interface. All six claims now have
unconditional proofs, collected by `RationalClockResearch.all_claims` in
`RationalClockResearch.lean`. They compile with Lean 4.33.0 and Mathlib at
the revision pinned by the root Lake manifest.

The finite-residue definition avoids presupposing a PadicInt digit-series API.
Periodic evaluation is proved directly against this definition; compatible
finite inverse clocks are also constructed. `low 0` below follows Mathlib's
total valuation convention and MUST NOT be used as the note's continuous
extension, which has low(0)=0.
The sums and positive orbits below never need a low-part evaluation at zero.
-/

namespace RationalClockResearch

def low (n : ℕ) : ℕ := 2 ^ padicValNat 2 n

def rulerSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => rulerSum n + low (n + 1)

def closed (c n : ℕ) : ℕ := n + 1 + 4 * c * rulerSum n

def step (c x : ℕ) : ℕ := x + 4 * c * low x + 1

def orbit (c seed : ℕ) : ℕ → ℕ
  | 0 => seed
  | t + 1 => step c (orbit c seed t)

/-- Equality to F_c(theta) expressed entirely through finite congruences. -/
def represents (c : ℕ) (theta : ℚ) (seed : ℤ) : Prop :=
  Odd theta.den ∧ ∀ K m : ℕ,
    Int.ModEq (2 ^ K) ((theta.den : ℤ) * (m : ℤ)) theta.num →
    Int.ModEq (2 ^ K) (closed c m : ℤ) seed

def hasRationalClock (c seed : ℕ) : Prop :=
  ∃ theta : ℚ, represents c theta (seed : ℤ)

/-- Common future, not equality of one-sided orbit lists. -/
def sameFuture (c a b : ℕ) : Prop :=
  ∃ m n : ℕ, orbit c a m = orbit c b n

def IntegralPhaseBoundClaim : Prop :=
  ∀ (c : ℕ) (theta : ℚ) (seed : ℤ), 0 < c →
    -(1 : ℚ) < theta → theta < 0 → represents c theta seed →
    (1 : ℤ) - (c : ℤ) ≤ seed ∧ seed ≤ (c : ℤ) ∧ seed ≠ 0 ∧ seed ≠ 1

def OriginalMapRigidityClaim : Prop :=
  ∀ seed : ℕ, 0 < seed →
    (hasRationalClock 1 seed ↔ ∃ m : ℕ, seed = closed 1 m)

def CoefficientTwelvePhaseClaim : Prop :=
  ∀ (theta : ℚ) (seed : ℤ), -(1 : ℚ) < theta → theta < 0 →
    (represents 3 theta seed ↔
      (theta = -(1 : ℚ) / 3 ∧ seed = 2) ∨
      (theta = -(2 : ℚ) / 3 ∧ seed = -1) ∨
      (theta = -(2 : ℚ) / 9 ∧ seed = 3) ∨
      (theta = -(7 : ℚ) / 9 ∧ seed = -2))

def FiveClassesClaim : Prop :=
  (∀ seed : ℕ, 0 < seed →
    (hasRationalClock 3 seed ↔
      sameFuture 3 seed 1 ∨ sameFuture 3 seed 2 ∨
      sameFuture 3 seed 12 ∨ sameFuture 3 seed 3 ∨ sameFuture 3 seed 23)) ∧
  (∀ a ∈ ([1, 2, 12, 3, 23] : List ℕ),
    ∀ b ∈ ([1, 2, 12, 3, 23] : List ℕ), sameFuture 3 a b → a = b)

def ValuationClocksClaim : Prop :=
  ∀ t : ℕ,
    padicValNat 2 (orbit 3 1 t) = padicValNat 2 (t + 1) ∧
    padicValNat 2 (orbit 3 2 t) = padicValNat 2 (3 * t + 2) ∧
    padicValNat 2 (orbit 3 12 t) = padicValNat 2 (3 * t + 4) ∧
    padicValNat 2 (orbit 3 3 t) = padicValNat 2 (9 * t + 7) ∧
    padicValNat 2 (orbit 3 23 t) = padicValNat 2 (9 * t + 11)

def ExactPowerHitsClaim : Prop :=
  ∀ t k : ℕ,
    (orbit 3 1 t = 2 ^ k ↔ t = 0 ∧ k = 0) ∧
    (orbit 3 2 t = 2 ^ k ↔ t = 0 ∧ k = 1) ∧
    orbit 3 12 t ≠ 2 ^ k ∧
    (orbit 3 3 t = 2 ^ k ↔ t = 1 ∧ k = 4) ∧
    orbit 3 23 t ≠ 2 ^ k

end RationalClockResearch

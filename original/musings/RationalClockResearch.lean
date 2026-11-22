import RationalClockPadicRational
import RationalClockPadicMeasure

/-!
# Verified rational-clock classification and 2-adic dynamics

This entry point checks all six claims against the original proposition
interface and imports the genuine 2-adic clock theorem. Each component is
unconditional; the finite-residue classification, uniform class bound,
isometric `ℤ_[2]` equivalence, explicit conjugacy, rational-point bridge,
exact finite-level equidistribution, and unique ergodicity are all in the
dependency graph.
-/

namespace RationalClockResearch

/-- The six statements of the rational-clock formalization, proved together. -/
theorem all_claims :
    IntegralPhaseBoundClaim ∧ OriginalMapRigidityClaim ∧
    CoefficientTwelvePhaseClaim ∧ FiveClassesClaim ∧
    ValuationClocksClaim ∧ ExactPowerHitsClaim :=
  ⟨integralPhaseBound, originalMapRigidity, coefficientTwelvePhase, fiveClasses,
    valuationClocks, exactPowerHits⟩

end RationalClockResearch

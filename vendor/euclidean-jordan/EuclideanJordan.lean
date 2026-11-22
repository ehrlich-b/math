/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import EuclideanJordan.Block
import EuclideanJordan.Bridge
import EuclideanJordan.Class
import EuclideanJordan.Connection
import EuclideanJordan.FormallyReal
import EuclideanJordan.Frame
import EuclideanJordan.FrameExists
import EuclideanJordan.FramePeirce
import EuclideanJordan.FramePeirceMul
import EuclideanJordan.HermitianBilin
import EuclideanJordan.HermitianCarrier
import EuclideanJordan.Order
import EuclideanJordan.OrderAuto
import EuclideanJordan.OrderUnitSpace
import EuclideanJordan.Orthogonal
import EuclideanJordan.Pattern
import EuclideanJordan.Peirce
import EuclideanJordan.PeirceMul
import EuclideanJordan.PeirceSubalgebra
import EuclideanJordan.Power
import EuclideanJordan.PowerAssoc
import EuclideanJordan.Rank
import EuclideanJordan.Spectral
import EuclideanJordan.Subalgebra
import EuclideanJordan.TraceForm
import EuclideanJordan.Vendor.ContinuousLinearMap
import EuclideanJordan.Vendor.HermitianMat.Basic
import EuclideanJordan.Vendor.HermitianMat.CFC
import EuclideanJordan.Vendor.HermitianMat.Inner
import EuclideanJordan.Vendor.HermitianMat.Jordan
import EuclideanJordan.Vendor.HermitianMat.NonSingular
import EuclideanJordan.Vendor.HermitianMat.Order
import EuclideanJordan.Vendor.HermitianMat.Proj
import EuclideanJordan.Vendor.HermitianMat.Reindex
import EuclideanJordan.Vendor.HermitianMat.Trace
import EuclideanJordan.Vendor.IsMaximalSelfAdjoint
import EuclideanJordan.Vendor.Isometry
import EuclideanJordan.Vendor.LinearEquiv
import EuclideanJordan.Vendor.Matrix
import EuclideanJordan.Vendor.Misc
import EuclideanJordan.Vendor.Tactic.Commutes
import EuclideanJordan.Vendor.Tactic.Commutes.Attribute
import EuclideanJordan.Witness

/-!
# Euclidean Jordan algebras in Lean 4

Root import for the library. See `README.md` for the headline results.

## Sources

* Jacques Faraut and Adam Korányi, *Analysis on Symmetric Cones* (1994),
DOI: 10.1093/oso/9780198534778.001.0001, §§III.1–III.2 and IV.1–IV.2.
* Abraham Adrian Albert, *Power-associative rings* (1948),
DOI: 10.1090/S0002-9947-1948-0027750-7, Theorem 2 (commutative power associativity).
* Erik M. Alfsen and Frederic W. Shultz, *Geometry of State Spaces of Operator
Algebras* (2003), DOI: 10.1007/978-1-4612-0019-2, Theorem 2.80.
-/

module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Convergence where

open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Iteration
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Estimates
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Invariants public

-- Geometric domination constructs a native Cauchy witness, without choosing
-- a modulus from a family of truncated continuity or differentiability data.
opaque
  dampedBishopPiHalfCauchy : DampedBishopPiHalfCauchy
  dampedBishopPiHalfCauchy = Estimates.cauchy dampedBishopPiHalfApproximation
    dampedBishopPiHalfApproximation-zero dampedBishopFirst dampedBishopStep
    dampedBishopPrefix dampedBishopIncreasing dampedBishopAfterFirst

opaque
  dampedBishopPiHalfLimit : DampedBishopPiHalfLimit
  dampedBishopPiHalfLimit = dampedBishopPiHalfLimitFromCauchy dampedBishopPiHalfCauchy

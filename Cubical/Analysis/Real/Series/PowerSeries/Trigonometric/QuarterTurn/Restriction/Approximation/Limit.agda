module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Limit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.IntervalLimit
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.ImageLimit


opaque
  sineQuarterApproximation→preimage : ∀ quarter target →
    SineQuarterApproximation quarter target →
    Σ[ point ∈ SineQuarterInterval quarter ]
      sinℝ (fst point) ≡ target
  sineQuarterApproximation→preimage
      quarter target (points , points-cauchy , image-limit) =
    sineQuarterSequenceLimitPointWith
      quarter points points-cauchy
      (λ value → sinℝ value ≡ target)
      (sineSequenceLimits-value
        (λ n → fst (points n))
        (sineQuarterSequenceLimit quarter points points-cauchy)
        target
        (sineQuarterSequenceLimit-converges
          quarter points points-cauchy)
        image-limit)

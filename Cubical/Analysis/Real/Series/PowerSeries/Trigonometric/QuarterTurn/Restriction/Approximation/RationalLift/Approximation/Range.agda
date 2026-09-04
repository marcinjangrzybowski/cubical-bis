module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.Range where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Order.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.IntervalLimit
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.Base


opaque
  rationalSineInverseApproximationCandidate-range :
    ∀ quarter (approximations :
      RationalSineInverseApproximationFamily quarter) →
    ∀ q →
    ((- quarter) ≤ℝ
      lim
        (λ n → fst (fst (approximations q) n))
        (fst (snd (approximations q))))
    ×
    (lim
      (λ n → fst (fst (approximations q) n))
      (fst (snd (approximations q)))
      ≤ℝ quarter)
  rationalSineInverseApproximationCandidate-range
      quarter approximations q =
    sineQuarterSequenceLimit-lower quarter
      (fst (approximations q))
      (fst (snd (approximations q)))
    , sineQuarterSequenceLimit-upper quarter
        (fst (approximations q))
        (fst (snd (approximations q)))

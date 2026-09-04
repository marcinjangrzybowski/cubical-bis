module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.Equation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.IntervalLimit
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.ImageLimit
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.Base


opaque
  rationalSineInverseApproximationCandidate-law :
    ∀ quarter (approximations :
      RationalSineInverseApproximationFamily quarter) →
    ∀ q →
    sinℝ
      (lim
        (λ n → fst (fst (approximations q) n))
        (fst (snd (approximations q))))
      ≡ unitClamp (rat q)
  rationalSineInverseApproximationCandidate-law
      quarter approximations q =
    sineSequenceLimit-value
      (λ n → fst (fst (approximations q) n))
      (fst (snd (approximations q)))
      (unitClamp (rat q))
      (snd (snd (approximations q)))

module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Estimates where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.LocalLipschitz
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base


opaque
  sineQuarterIntervalAbsBound : ∀ quarter →
    (point : SineQuarterInterval quarter) → absℝ (fst point) ≤ℝ quarter
  sineQuarterIntervalAbsBound quarter point =
    absLeastUpperBound (fst point) quarter (snd (snd point))
      (subst ((- fst point) ≤ℝ_) (negInvol quarter)
        (negPres≤ (- quarter) (fst point) (fst (snd point))))


  sineQuarterOrderedDifferenceBound : ∀ quarter → 0ℝ ≤ℝ quarter →
    (left right : SineQuarterInterval quarter) → fst left ≤ℝ fst right →
    absℝ (sinℝ (fst right) - sinℝ (fst left)) ≤ℝ
      (fst right - fst left) · exponentialEntireValue quarter
  sineQuarterOrderedDifferenceBound quarter nonnegative left right ordered =
    subst (absℝ (sinℝ (fst right) - sinℝ (fst left)) ≤ℝ_)
      (cong (_· exponentialEntireValue quarter)
        (absOfNonnegative (fst right - fst left)
          (nonnegativeSub (fst left) (fst right) ordered)))
      (sinℝ-absoluteDifferenceBoundOnRadius
        (fst left) (fst right) quarter nonnegative
        (sineQuarterIntervalAbsBound quarter left)
        (sineQuarterIntervalAbsBound quarter right))

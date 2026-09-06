module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Density where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; _+₊_; ℚ₊≡)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Density
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Initial
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Step
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Width
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Iteration
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Error
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Estimates


-- Approximate surjectivity needs only the quarter-turn endpoint values and
-- a nonnegative quarter.  Monotonicity and countable choice are not used.
-- Exact intermediate values still require a constructive source sequence
-- with a native Cauchy witness; finite density alone does not supply it.
sineQuarterApproximateImageDensityByBisection : ∀ quarter →
  IsPositiveQuarterTurn quarter → 0ℝ ≤ℝ quarter →
  SineQuarterApproximateImageDensity quarter
sineQuarterApproximateImageDensityByBisection
    quarter positive-quarter nonnegative target lower upper tolerance =
  PT.rec squash₁ atDepth
    (iteratedHalvingProductEventuallySmall
      (sineQuarterBracketWidth quarter target slack initial)
      (exponentialEntireValue quarter) slack)
  where
  slack : ℚ₊
  slack = tolerance /2₊

  initial : SineQuarterSlackBracket quarter target slack
  initial = sineQuarterInitialSlackBracket
    quarter positive-quarter nonnegative target lower upper slack

  half-width : ℕ → ℝ
  half-width n = iteratedHalving n
    (sineQuarterBracketWidth quarter target slack initial)

  approximate : ∀ n →
    half-width n · exponentialEntireValue quarter <ℝ rat (fst slack) →
    (Σ[ bracket ∈ SineQuarterSlackBracket quarter target slack ]
      sineQuarterBracketWidth quarter target slack bracket ≡ half-width n) →
    SineQuarterApproximatePreimage quarter target tolerance
  approximate n small ((left , right , ordered , below , above) , width) =
    left
    , subst (λ radius → sinℝ (fst left) ∼[ radius ] target)
        (ℚ₊≡ (1/2∈ℚ./2+/2≡id (fst tolerance)))
        (slackBracketImagesClose
          (sinℝ (fst left)) (sinℝ (fst right)) target slack below above
          (≤<ℝ-trans
            (absℝ (sinℝ (fst right) - sinℝ (fst left)))
            ((fst right - fst left) · exponentialEntireValue quarter)
            (rat (fst slack))
            (sineQuarterOrderedDifferenceBound
              quarter nonnegative left right ordered)
            (subst (_<ℝ rat (fst slack))
              (cong (_· exponentialEntireValue quarter) (sym width)) small)))

  atDepth :
    (Σ[ n ∈ ℕ ]
      half-width n · exponentialEntireValue quarter <ℝ rat (fst slack)) →
    ∥ SineQuarterApproximatePreimage quarter target tolerance ∥₁
  atDepth (n , small) =
    PT.map (approximate n small)
      (sineQuarterSlackBracketRefine quarter target slack initial n)

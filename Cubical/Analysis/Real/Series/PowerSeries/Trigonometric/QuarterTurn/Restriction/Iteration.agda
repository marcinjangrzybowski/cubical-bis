module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Iteration where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Functions.Inverse.Iteration.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.NonExpanding
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Quantitative
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Sequence.Chosen
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Endpoints
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Surjectivity
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Limit

private
  opaque
    directedBound : ∀ (f : ℝ → ℝ) →
      (∀ x y → absℝ (f x - f y) ≤ℝ absℝ (x - y)) →
      ∀ x y → x ≤ℝ y → f x - f y ≤ℝ y - x
    directedBound f bounded x y ordered =
      ≤ℝ-trans (f x - f y) (absℝ (f x - f y)) (y - x)
        (leAbs (f x - f y))
        (subst (absℝ (f x - f y) ≤ℝ_)
          (absSubComm x y ∙ absOfNonnegative (y - x) (nonnegativeSub x y ordered))
          (bounded x y))

    upperDirectedBound : ∀ (f : ℝ → ℝ) →
      (∀ x y → absℝ (f x - f y) ≤ℝ absℝ (x - y)) →
      ∀ x y → x ≤ℝ y → f y - f x ≤ℝ y - x
    upperDirectedBound f bounded x y ordered =
      ≤ℝ-trans (f y - f x) (absℝ (f y - f x)) (y - x)
        (leAbs (f y - f x))
        (subst (absℝ (f y - f x) ≤ℝ_)
          (absOfNonnegative (y - x) (nonnegativeSub x y ordered))
          (bounded y x))

    unpackStrictIncrease : ∀ (f : ℝ → ℝ) a b →
      (∀ (left right : ClosedInterval a b) → fst left <ℝ fst right →
        f (fst left) <ℝ f (fst right)) →
      ∀ x y → a ≤ℝ x → x <ℝ y → y ≤ℝ b → f x <ℝ f y
    unpackStrictIncrease f a b increasing x y left strict right =
      increasing
        (x , left , ≤ℝ-trans x y b (<ℝ-weaken x y strict) right)
        (y , ≤ℝ-trans a x y left (<ℝ-weaken x y strict) , right) strict

    weakIncrease : ∀ (f : ℝ → ℝ) (a b : ℝ) →
      (∀ x y → absℝ (f x - f y) ≤ℝ absℝ (x - y)) →
      (∀ x y → a ≤ℝ x → x <ℝ y → y ≤ℝ b → f x <ℝ f y) →
      ∀ x y → a ≤ℝ x → x ≤ℝ y → y ≤ℝ b → f x ≤ℝ f y
    weakIncrease f a b bounded increasing x y left ordered right =
      notGreater→≤ℝ (f x) (f y) λ reversed →
        <ℝ-asym (f x) (f y)
          (increasing x y left
            (positiveSub→< x y
              (<≤ℝ-trans 0ℝ (f x - f y) (y - x)
                (positiveSub (f y) (f x) reversed)
                (directedBound f bounded x y ordered))) right) reversed

  opaque
    assembleApproximation : ∀ quarter target →
      ChosenQuarterTurnSineClosenessReflectionModulus quarter →
      (Σ[ points ∈ (ℕ → SineQuarterInterval quarter) ]
        SeqWitness (λ n → sinℝ (fst (points n))) ×
        isLimitSequence (λ n → sinℝ (fst (points n))) target) →
      SineQuarterApproximation quarter target
    assembleApproximation quarter target modulus (points , witness , limit) =
      points , chosenSineClosenessReflection-presSeqWitness quarter modulus points witness , limit

  module Construction (quarter : ℝ) (turn : IsPositiveQuarterTurn quarter)
    (first : IsFirstPositiveCosineZero quarter)
    (target : ℝ) (low : (- 1ℝ) ≤ℝ target) (high : target ≤ℝ 1ℝ) where

    opaque
      ordered : (- quarter) ≤ℝ quarter
      ordered = sineQuarterEndpointsOrdered quarter
        (<ℝ-weaken 0ℝ quarter (firstPositiveCosineZero-positive first))

      low-image : sinℝ (- quarter) ≤ℝ target
      low-image = subst (_≤ℝ target) (sym (sinℝ-negativeQuarter quarter turn)) low

      high-image : target ≤ℝ sinℝ quarter
      high-image = subst (target ≤ℝ_) (sym (sinℝ-positiveQuarter quarter turn)) high

      monotone : ∀ x y → (- quarter) ≤ℝ x → x ≤ℝ y → y ≤ℝ quarter →
        sinℝ x ≤ℝ sinℝ y
      monotone = weakIncrease sinℝ (- quarter) quarter sinℝ-difference-bound
        (unpackStrictIncrease sinℝ (- quarter) quarter
          (sinℝ-strictMonotone-on-quarterInterval quarter turn first))

      upper-difference : ∀ x y → (- quarter) ≤ℝ x → x ≤ℝ y → y ≤ℝ quarter →
        sinℝ y - sinℝ x ≤ℝ y - x
      upper-difference x y left ordered right =
        upperDirectedBound sinℝ sinℝ-difference-bound x y ordered

    module C = Convergence sinℝ (- quarter) quarter target ordered low-image high-image
      monotone upper-difference

    opaque
      approximation : SineQuarterApproximation quarter target
      approximation = assembleApproximation quarter target
        (characterizedQuarterTurn-chosenSineClosenessReflectionModulus quarter turn first)
        C.convergentIntervalImages

opaque
  sineQuarterApproximationByIteration : ∀ quarter →
    IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
    ∀ target → (- 1ℝ) ≤ℝ target → target ≤ℝ 1ℝ →
    SineQuarterApproximation quarter target
  sineQuarterApproximationByIteration = Construction.approximation

opaque
  sineQuarterPreimageByIteration : ∀ quarter →
    IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
    ∀ target → (- 1ℝ) ≤ℝ target → target ≤ℝ 1ℝ →
    Σ[ point ∈ SineQuarterInterval quarter ] sinℝ (fst point) ≡ target
  sineQuarterPreimageByIteration quarter turn first target low high =
    sineQuarterApproximation→preimage quarter target
      (sineQuarterApproximationByIteration quarter turn first target low high)

opaque
  sineQuarterIntermediateValueByIteration : ∀ quarter →
    IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
    SineQuarterIntermediateValue quarter
  sineQuarterIntermediateValueByIteration quarter turn first target low high =
    ∣ sineQuarterPreimageByIteration quarter turn first target low high ∣₁

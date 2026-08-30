module Cubical.Analysis.Real.Calculus.Derivative.Quotient where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Product
open import Cubical.Analysis.Real.Calculus.Derivative.Reciprocal


-- Quotient rules are first exposed on a domain carrying one fixed positive
-- rational denominator bound.  This keeps the inverse estimate explicit and
-- avoids eliminating pointwise positivity inside every derivative witness.
lowerBoundedPositiveDivideByCoordinate :
  ∀ η → (LowerBoundedPositive η → ℝ) →
  LowerBoundedPositive η → ℝ
lowerBoundedPositiveDivideByCoordinate η numerator point =
  numerator point · lowerBoundedPositiveReciprocal η point


lowerBoundedPositiveDivideByCoordinateDerivative :
  ∀ η →
  (numerator numeratorDerivative : LowerBoundedPositive η → ℝ) →
  LowerBoundedPositive η → ℝ
lowerBoundedPositiveDivideByCoordinateDerivative
    η numerator numeratorDerivative point =
  numeratorDerivative point
    · lowerBoundedPositiveReciprocal η point
  + numerator point
    · lowerBoundedPositiveReciprocalDerivative η point


lowerBoundedPositiveDivideByCoordinateHasDerivativeAlong :
  ∀ η
    (numerator numeratorDerivative : LowerBoundedPositive η → ℝ) →
  IsDerivativeAlong
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveCoordinate η)
    numerator numeratorDerivative →
  IsDerivativeAlong
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveCoordinate η)
    (lowerBoundedPositiveDivideByCoordinate η numerator)
    (lowerBoundedPositiveDivideByCoordinateDerivative
      η numerator numeratorDerivative)
lowerBoundedPositiveDivideByCoordinateHasDerivativeAlong
    η numerator numeratorDerivative numerator-has-derivative =
  mulHasDerivativeAlong
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveCoordinate η)
    numerator
    (lowerBoundedPositiveReciprocal η)
    numeratorDerivative
    (lowerBoundedPositiveReciprocalDerivative η)
    (lowerBoundedPositiveCoordinateIsContinuous η)
    numerator-has-derivative
    (lowerBoundedPositiveReciprocalHasDerivativeAlong η)


positiveDivideByCoordinateOnLowerBound :
  ∀ η → (LowerBoundedPositive η → ℝ) →
  LowerBoundedPositive η → ℝ
positiveDivideByCoordinateOnLowerBound η numerator point =
  numerator point · positiveReciprocalOnLowerBound η point


positiveDivideByCoordinateOnLowerBoundDerivative :
  ∀ η →
  (numerator numeratorDerivative : LowerBoundedPositive η → ℝ) →
  LowerBoundedPositive η → ℝ
positiveDivideByCoordinateOnLowerBoundDerivative
    η numerator numeratorDerivative point =
  numeratorDerivative point
    · positiveReciprocalOnLowerBound η point
  + numerator point
    · positiveReciprocalOnLowerBoundDerivative η point


positiveDivideByCoordinateOnLowerBoundHasDerivativeAlong :
  ∀ η
    (numerator numeratorDerivative : LowerBoundedPositive η → ℝ) →
  IsDerivativeAlong
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveCoordinate η)
    numerator numeratorDerivative →
  IsDerivativeAlong
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveCoordinate η)
    (positiveDivideByCoordinateOnLowerBound η numerator)
    (positiveDivideByCoordinateOnLowerBoundDerivative
      η numerator numeratorDerivative)
positiveDivideByCoordinateOnLowerBoundHasDerivativeAlong
    η numerator numeratorDerivative numerator-has-derivative =
  mulHasDerivativeAlong
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveCoordinate η)
    numerator
    (positiveReciprocalOnLowerBound η)
    numeratorDerivative
    (positiveReciprocalOnLowerBoundDerivative η)
    (lowerBoundedPositiveCoordinateIsContinuous η)
    numerator-has-derivative
    (positiveReciprocalOnLowerBoundHasDerivativeAlong η)

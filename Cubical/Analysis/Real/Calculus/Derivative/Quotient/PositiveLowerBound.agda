module Cubical.Analysis.Real.Calculus.Derivative.Quotient.PositiveLowerBound where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Continuity
open import Cubical.Analysis.Real.Calculus.Derivative.Chain.Indexed
open import Cubical.Analysis.Real.Calculus.Derivative.Product
open import Cubical.Analysis.Real.Calculus.Derivative.Reciprocal

open PositiveRationals using (ℚ₊)


private
  variable
    ℓ ℓ' : Level


-- The proof component of the lower-bounded target does not occur in its
-- inherited closeness.  Thus continuity of the real denominator coordinate
-- is exactly continuity of the subtype-valued denominator map.

lowerBoundedMapOfDerivativeIsContinuous :
  ∀ {A : Type ℓ}
    (η : ℚ₊)
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ)
    (denominator : A → LowerBoundedPositive η)
    (denominator-derivative : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong
    source coordinate
    (lowerBoundedPositiveCoordinate η ∘ denominator)
    denominator-derivative →
  isContinuous
    source denominator
    (LowerBoundedPositivePremetricSpace η .snd)
lowerBoundedMapOfDerivativeIsContinuous
  η source coordinate denominator denominator-derivative
  coordinate-continuous denominator-has-derivative
  point .IsContinuousAt.pres≈ ε =
    derivativeAlongIsContinuous
        source coordinate
        (lowerBoundedPositiveCoordinate η ∘ denominator)
        denominator-derivative
        coordinate-continuous
        denominator-has-derivative
        point
      .IsContinuousAt.pres≈ ε


reciprocalOfLowerBoundedMap :
  ∀ {A : Type ℓ} η →
  (A → LowerBoundedPositive η) → A → ℝ
reciprocalOfLowerBoundedMap η denominator =
  positiveReciprocalOnLowerBound η ∘ denominator


reciprocalOfLowerBoundedMapDerivative :
  ∀ {A : Type ℓ} η
    (denominator : A → LowerBoundedPositive η) →
  (A → ℝ) → A → ℝ
reciprocalOfLowerBoundedMapDerivative
  η denominator denominator-derivative point =
  positiveReciprocalOnLowerBoundDerivative
      η (denominator point)
    · denominator-derivative point


reciprocalOfLowerBoundedMapHasDerivativeAlong :
  ∀ {A : Type ℓ}
    (η : ℚ₊)
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ)
    (denominator : A → LowerBoundedPositive η)
    (denominator-derivative : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong
    source coordinate
    (lowerBoundedPositiveCoordinate η ∘ denominator)
    denominator-derivative →
  IsDerivativeAlong
    source coordinate
    (reciprocalOfLowerBoundedMap η denominator)
    (reciprocalOfLowerBoundedMapDerivative
      η denominator denominator-derivative)
reciprocalOfLowerBoundedMapHasDerivativeAlong
  η source coordinate denominator denominator-derivative
  coordinate-continuous denominator-has-derivative =
  chainHasDerivativeAlongIndexed
    source coordinate
    (lowerBoundedPositiveCoordinate η ∘ denominator)
    denominator-derivative
    (reciprocalOfLowerBoundedMap η denominator)
    (positiveReciprocalOnLowerBoundDerivative η ∘ denominator)
    denominator-has-derivative
    reciprocal-along-denominator
  where
  denominator-continuous :
    isContinuous
      source denominator
      (LowerBoundedPositivePremetricSpace η .snd)
  denominator-continuous =
    lowerBoundedMapOfDerivativeIsContinuous
      η source coordinate denominator denominator-derivative
      coordinate-continuous denominator-has-derivative

  reciprocal-along-denominator :
    IsDerivativeAlong
      source
      (lowerBoundedPositiveCoordinate η ∘ denominator)
      (reciprocalOfLowerBoundedMap η denominator)
      (positiveReciprocalOnLowerBoundDerivative η ∘ denominator)
  reciprocal-along-denominator =
    pullbackHasDerivativeAlong
      source
      (LowerBoundedPositivePremetricSpace η .snd)
      (lowerBoundedPositiveCoordinate η)
      (positiveReciprocalOnLowerBound η)
      (positiveReciprocalOnLowerBoundDerivative η)
      denominator
      denominator-continuous
      (positiveReciprocalOnLowerBoundHasDerivativeAlong η)


quotientByLowerBoundedMap :
  ∀ {A : Type ℓ} η →
  (A → ℝ) → (A → LowerBoundedPositive η) → A → ℝ
quotientByLowerBoundedMap η numerator denominator point =
  numerator point ·
    reciprocalOfLowerBoundedMap η denominator point


quotientByLowerBoundedMapDerivative :
  ∀ {A : Type ℓ} η
    (numerator : A → ℝ)
    (denominator : A → LowerBoundedPositive η)
    (numerator-derivative denominator-derivative : A → ℝ) →
  A → ℝ
quotientByLowerBoundedMapDerivative
  η numerator denominator
  numerator-derivative denominator-derivative point =
  numerator-derivative point ·
      reciprocalOfLowerBoundedMap η denominator point
    +
  numerator point ·
      reciprocalOfLowerBoundedMapDerivative
        η denominator denominator-derivative point


quotientByLowerBoundedMapHasDerivativeAlong :
  ∀ {A : Type ℓ}
    (η : ℚ₊)
    (source : PremetricStr ℓ' A)
    (coordinate numerator : A → ℝ)
    (denominator : A → LowerBoundedPositive η)
    (numerator-derivative denominator-derivative : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong
    source coordinate numerator numerator-derivative →
  IsDerivativeAlong
    source coordinate
    (lowerBoundedPositiveCoordinate η ∘ denominator)
    denominator-derivative →
  IsDerivativeAlong
    source coordinate
    (quotientByLowerBoundedMap η numerator denominator)
    (quotientByLowerBoundedMapDerivative
      η numerator denominator
      numerator-derivative denominator-derivative)
quotientByLowerBoundedMapHasDerivativeAlong
  η source coordinate numerator denominator
  numerator-derivative denominator-derivative
  coordinate-continuous
  numerator-has-derivative denominator-has-derivative =
  mulHasDerivativeAlong
    source coordinate
    numerator
    (reciprocalOfLowerBoundedMap η denominator)
    numerator-derivative
    (reciprocalOfLowerBoundedMapDerivative
      η denominator denominator-derivative)
    coordinate-continuous
    numerator-has-derivative
    (reciprocalOfLowerBoundedMapHasDerivativeAlong
      η source coordinate denominator denominator-derivative
      coordinate-continuous denominator-has-derivative)


-- Convenience surface for an ordinary real denominator together with its
-- explicit uniform positive lower bound.

lowerBoundedDenominatorMap :
  ∀ {A : Type ℓ} η
    (denominator : A → ℝ) →
  (∀ point → rat (fst η) ≤ℝ denominator point) →
  A → LowerBoundedPositive η
lowerBoundedDenominatorMap η denominator denominator-lower point =
  denominator point , denominator-lower point


positiveLowerBoundDenominatorIsPositive :
  ∀ {A : Type ℓ} η
    (denominator : A → ℝ)
    (denominator-lower :
      ∀ point → rat (fst η) ≤ℝ denominator point) →
  ∀ point → 0ℝ <ℝ denominator point
positiveLowerBoundDenominatorIsPositive
  η denominator denominator-lower point =
  lowerBoundedPositiveIsPositive η
    (lowerBoundedDenominatorMap
      η denominator denominator-lower point)


divideByPositiveLowerBound :
  ∀ {A : Type ℓ} η
    (numerator denominator : A → ℝ)
    (denominator-lower :
      ∀ point → rat (fst η) ≤ℝ denominator point) →
  A → ℝ
divideByPositiveLowerBound
  η numerator denominator denominator-lower point =
  numerator point ·
    positiveReciprocal
      (denominator point)
      (positiveLowerBoundDenominatorIsPositive
        η denominator denominator-lower point)


divideByPositiveLowerBoundDerivative :
  ∀ {A : Type ℓ} η
    (numerator denominator : A → ℝ)
    (denominator-lower :
      ∀ point → rat (fst η) ≤ℝ denominator point)
    (numerator-derivative denominator-derivative : A → ℝ) →
  A → ℝ
divideByPositiveLowerBoundDerivative
  η numerator denominator denominator-lower
  numerator-derivative denominator-derivative point =
  let
    reciprocal =
      positiveReciprocal
        (denominator point)
        (positiveLowerBoundDenominatorIsPositive
          η denominator denominator-lower point)
  in
  numerator-derivative point · reciprocal
    + numerator point ·
        ((- (reciprocal · reciprocal)) ·
          denominator-derivative point)


divideByPositiveLowerBoundHasDerivativeAlong :
  ∀ {A : Type ℓ}
    (η : ℚ₊)
    (source : PremetricStr ℓ' A)
    (coordinate numerator denominator : A → ℝ)
    (denominator-lower :
      ∀ point → rat (fst η) ≤ℝ denominator point)
    (numerator-derivative denominator-derivative : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong
    source coordinate numerator numerator-derivative →
  IsDerivativeAlong
    source coordinate denominator denominator-derivative →
  IsDerivativeAlong
    source coordinate
    (divideByPositiveLowerBound
      η numerator denominator denominator-lower)
    (divideByPositiveLowerBoundDerivative
      η numerator denominator denominator-lower
      numerator-derivative denominator-derivative)
divideByPositiveLowerBoundHasDerivativeAlong
  η source coordinate numerator denominator denominator-lower
  numerator-derivative denominator-derivative
  coordinate-continuous
  numerator-has-derivative denominator-has-derivative =
  quotientByLowerBoundedMapHasDerivativeAlong
    η source coordinate numerator
    (lowerBoundedDenominatorMap
      η denominator denominator-lower)
    numerator-derivative denominator-derivative
    coordinate-continuous
    numerator-has-derivative denominator-has-derivative


divideByPositiveLowerBoundHasDerivative :
  ∀ η
    (numerator denominator : ℝ → ℝ)
    (denominator-lower :
      ∀ point → rat (fst η) ≤ℝ denominator point)
    (numerator-derivative denominator-derivative : ℝ → ℝ) →
  IsDerivative numerator numerator-derivative →
  IsDerivative denominator denominator-derivative →
  IsDerivative
    (divideByPositiveLowerBound
      η numerator denominator denominator-lower)
    (divideByPositiveLowerBoundDerivative
      η numerator denominator denominator-lower
      numerator-derivative denominator-derivative)
divideByPositiveLowerBoundHasDerivative
  η numerator denominator denominator-lower
  numerator-derivative denominator-derivative =
  divideByPositiveLowerBoundHasDerivativeAlong
    η (ℝPremetricSpace .snd) (idfun ℝ)
    numerator denominator denominator-lower
    numerator-derivative denominator-derivative
    (snd (CategoryStructures.idᶜ {M = ℝPremetricSpace}))

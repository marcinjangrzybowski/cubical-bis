module Cubical.Analysis.Real.Calculus.Derivative.Quotient.NegativeUpperBound where

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
open import Cubical.Analysis.Real.Calculus.Derivative.SignedReciprocal

open PositiveRationals using (ℚ₊)


private
  variable
    ℓ ℓ' : Level


-- The proof component of the upper-bounded target does not occur in its
-- inherited closeness.  Thus continuity of the real denominator coordinate
-- is exactly continuity of the subtype-valued denominator map.

upperBoundedMapOfDerivativeIsContinuous :
  ∀ {A : Type ℓ}
    (η : ℚ₊)
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ)
    (denominator : A → UpperBoundedNegative η)
    (denominator-derivative : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong
    source coordinate
    (upperBoundedNegativeCoordinate η ∘ denominator)
    denominator-derivative →
  isContinuous
    source denominator
    (UpperBoundedNegativePremetricSpace η .snd)
upperBoundedMapOfDerivativeIsContinuous
  η source coordinate denominator denominator-derivative
  coordinate-continuous denominator-has-derivative
  point .IsContinuousAt.pres≈ ε =
    derivativeAlongIsContinuous
        source coordinate
        (upperBoundedNegativeCoordinate η ∘ denominator)
        denominator-derivative
        coordinate-continuous
        denominator-has-derivative
        point
      .IsContinuousAt.pres≈ ε


reciprocalOfUpperBoundedMap :
  ∀ {A : Type ℓ} η →
  (A → UpperBoundedNegative η) → A → ℝ
reciprocalOfUpperBoundedMap η denominator =
  upperBoundedNegativeReciprocal η ∘ denominator


reciprocalOfUpperBoundedMapDerivative :
  ∀ {A : Type ℓ} η
    (denominator : A → UpperBoundedNegative η) →
  (A → ℝ) → A → ℝ
reciprocalOfUpperBoundedMapDerivative
  η denominator denominator-derivative point =
  upperBoundedNegativeReciprocalDerivative
      η (denominator point)
    · denominator-derivative point


reciprocalOfUpperBoundedMapHasDerivativeAlong :
  ∀ {A : Type ℓ}
    (η : ℚ₊)
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ)
    (denominator : A → UpperBoundedNegative η)
    (denominator-derivative : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong
    source coordinate
    (upperBoundedNegativeCoordinate η ∘ denominator)
    denominator-derivative →
  IsDerivativeAlong
    source coordinate
    (reciprocalOfUpperBoundedMap η denominator)
    (reciprocalOfUpperBoundedMapDerivative
      η denominator denominator-derivative)
reciprocalOfUpperBoundedMapHasDerivativeAlong
  η source coordinate denominator denominator-derivative
  coordinate-continuous denominator-has-derivative =
  chainHasDerivativeAlongIndexed
    source coordinate
    (upperBoundedNegativeCoordinate η ∘ denominator)
    denominator-derivative
    (reciprocalOfUpperBoundedMap η denominator)
    (upperBoundedNegativeReciprocalDerivative η ∘ denominator)
    denominator-has-derivative
    reciprocal-along-denominator
  where
  denominator-continuous :
    isContinuous
      source denominator
      (UpperBoundedNegativePremetricSpace η .snd)
  denominator-continuous =
    upperBoundedMapOfDerivativeIsContinuous
      η source coordinate denominator denominator-derivative
      coordinate-continuous denominator-has-derivative

  reciprocal-along-denominator :
    IsDerivativeAlong
      source
      (upperBoundedNegativeCoordinate η ∘ denominator)
      (reciprocalOfUpperBoundedMap η denominator)
      (upperBoundedNegativeReciprocalDerivative η ∘ denominator)
  reciprocal-along-denominator =
    pullbackHasDerivativeAlong
      source
      (UpperBoundedNegativePremetricSpace η .snd)
      (upperBoundedNegativeCoordinate η)
      (upperBoundedNegativeReciprocal η)
      (upperBoundedNegativeReciprocalDerivative η)
      denominator
      denominator-continuous
      (upperBoundedNegativeReciprocalHasDerivativeAlong η)


quotientByUpperBoundedMap :
  ∀ {A : Type ℓ} η →
  (A → ℝ) → (A → UpperBoundedNegative η) → A → ℝ
quotientByUpperBoundedMap η numerator denominator point =
  numerator point ·
    reciprocalOfUpperBoundedMap η denominator point


quotientByUpperBoundedMapDerivative :
  ∀ {A : Type ℓ} η
    (numerator : A → ℝ)
    (denominator : A → UpperBoundedNegative η)
    (numerator-derivative denominator-derivative : A → ℝ) →
  A → ℝ
quotientByUpperBoundedMapDerivative
  η numerator denominator
  numerator-derivative denominator-derivative point =
  numerator-derivative point ·
      reciprocalOfUpperBoundedMap η denominator point
    +
  numerator point ·
      reciprocalOfUpperBoundedMapDerivative
        η denominator denominator-derivative point


quotientByUpperBoundedMapHasDerivativeAlong :
  ∀ {A : Type ℓ}
    (η : ℚ₊)
    (source : PremetricStr ℓ' A)
    (coordinate numerator : A → ℝ)
    (denominator : A → UpperBoundedNegative η)
    (numerator-derivative denominator-derivative : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong
    source coordinate numerator numerator-derivative →
  IsDerivativeAlong
    source coordinate
    (upperBoundedNegativeCoordinate η ∘ denominator)
    denominator-derivative →
  IsDerivativeAlong
    source coordinate
    (quotientByUpperBoundedMap η numerator denominator)
    (quotientByUpperBoundedMapDerivative
      η numerator denominator
      numerator-derivative denominator-derivative)
quotientByUpperBoundedMapHasDerivativeAlong
  η source coordinate numerator denominator
  numerator-derivative denominator-derivative
  coordinate-continuous
  numerator-has-derivative denominator-has-derivative =
  mulHasDerivativeAlong
    source coordinate
    numerator
    (reciprocalOfUpperBoundedMap η denominator)
    numerator-derivative
    (reciprocalOfUpperBoundedMapDerivative
      η denominator denominator-derivative)
    coordinate-continuous
    numerator-has-derivative
    (reciprocalOfUpperBoundedMapHasDerivativeAlong
      η source coordinate denominator denominator-derivative
      coordinate-continuous denominator-has-derivative)


-- Convenience surface for an ordinary real denominator together with its
-- explicit uniform negative upper bound.

upperBoundedDenominatorMap :
  ∀ {A : Type ℓ} η
    (denominator : A → ℝ) →
  (∀ point → denominator point ≤ℝ - rat (fst η)) →
  A → UpperBoundedNegative η
upperBoundedDenominatorMap η denominator denominator-upper point =
  denominator point , denominator-upper point


negativeUpperBoundDenominatorIsNegative :
  ∀ {A : Type ℓ} η
    (denominator : A → ℝ)
    (denominator-upper :
      ∀ point → denominator point ≤ℝ - rat (fst η)) →
  ∀ point → denominator point <ℝ 0ℝ
negativeUpperBoundDenominatorIsNegative
  η denominator denominator-upper point =
  upperBoundedNegativeIsNegative η
    (upperBoundedDenominatorMap
      η denominator denominator-upper point)


divideByNegativeUpperBound :
  ∀ {A : Type ℓ} η
    (numerator denominator : A → ℝ)
    (denominator-upper :
      ∀ point → denominator point ≤ℝ - rat (fst η)) →
  A → ℝ
divideByNegativeUpperBound
  η numerator denominator denominator-upper point =
  numerator point ·
    upperBoundedNegativeReciprocal η
      (upperBoundedDenominatorMap
        η denominator denominator-upper point)


divideByNegativeUpperBoundDerivative :
  ∀ {A : Type ℓ} η
    (numerator denominator : A → ℝ)
    (denominator-upper :
      ∀ point → denominator point ≤ℝ - rat (fst η))
    (numerator-derivative denominator-derivative : A → ℝ) →
  A → ℝ
divideByNegativeUpperBoundDerivative
  η numerator denominator denominator-upper
  numerator-derivative denominator-derivative point =
  let
    reciprocal =
      upperBoundedNegativeReciprocal η
        (upperBoundedDenominatorMap
          η denominator denominator-upper point)
  in
  numerator-derivative point · reciprocal
    + numerator point ·
        ((- (reciprocal · reciprocal)) ·
          denominator-derivative point)


divideByNegativeUpperBoundHasDerivativeAlong :
  ∀ {A : Type ℓ}
    (η : ℚ₊)
    (source : PremetricStr ℓ' A)
    (coordinate numerator denominator : A → ℝ)
    (denominator-upper :
      ∀ point → denominator point ≤ℝ - rat (fst η))
    (numerator-derivative denominator-derivative : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong
    source coordinate numerator numerator-derivative →
  IsDerivativeAlong
    source coordinate denominator denominator-derivative →
  IsDerivativeAlong
    source coordinate
    (divideByNegativeUpperBound
      η numerator denominator denominator-upper)
    (divideByNegativeUpperBoundDerivative
      η numerator denominator denominator-upper
      numerator-derivative denominator-derivative)
divideByNegativeUpperBoundHasDerivativeAlong
  η source coordinate numerator denominator denominator-upper
  numerator-derivative denominator-derivative
  coordinate-continuous
  numerator-has-derivative denominator-has-derivative =
  quotientByUpperBoundedMapHasDerivativeAlong
    η source coordinate numerator
    (upperBoundedDenominatorMap
      η denominator denominator-upper)
    numerator-derivative denominator-derivative
    coordinate-continuous
    numerator-has-derivative denominator-has-derivative


divideByNegativeUpperBoundHasDerivative :
  ∀ η
    (numerator denominator : ℝ → ℝ)
    (denominator-upper :
      ∀ point → denominator point ≤ℝ - rat (fst η))
    (numerator-derivative denominator-derivative : ℝ → ℝ) →
  IsDerivative numerator numerator-derivative →
  IsDerivative denominator denominator-derivative →
  IsDerivative
    (divideByNegativeUpperBound
      η numerator denominator denominator-upper)
    (divideByNegativeUpperBoundDerivative
      η numerator denominator denominator-upper
      numerator-derivative denominator-derivative)
divideByNegativeUpperBoundHasDerivative
  η numerator denominator denominator-upper
  numerator-derivative denominator-derivative =
  divideByNegativeUpperBoundHasDerivativeAlong
    η (ℝPremetricSpace .snd) (idfun ℝ)
    numerator denominator denominator-upper
    numerator-derivative denominator-derivative
    (snd (CategoryStructures.idᶜ {M = ℝPremetricSpace}))

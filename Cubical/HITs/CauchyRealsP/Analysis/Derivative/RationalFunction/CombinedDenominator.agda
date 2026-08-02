module Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.CombinedDenominator where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Algebra
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Domain
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.NormalForm
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Operations

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

  rearrangeFourFactors :
    ∀ (a b c d : ℝ) →
    (a · b) · (c · d) ≡
    (a · c) · (b · d)
  rearrangeFourFactors a b c d =
    mulAssoc a b (c · d)
    ∙ cong (a ·_)
        (sym (mulAssoc b c d))
    ∙ cong (λ value → a · (value · d))
        (mulComm b c)
    ∙ cong (a ·_)
        (mulAssoc c b d)
    ∙ sym (mulAssoc a c (b · d))

  addFractionsAlgebra :
    ∀ left-numerator left-denominator
      right-numerator right-denominator
      left-inverse right-inverse →
    left-denominator · left-inverse ≡ 1 →
    right-denominator · right-inverse ≡ 1 →
    ( left-numerator · right-denominator
        + right-numerator · left-denominator
    ) · (left-inverse · right-inverse)
      ≡
    left-numerator · left-inverse
      + right-numerator · right-inverse
  addFractionsAlgebra
    left-numerator left-denominator
    right-numerator right-denominator
    left-inverse right-inverse
    left-law right-law =
      mulDistL
        (left-numerator · right-denominator)
        (right-numerator · left-denominator)
        (left-inverse · right-inverse)
      ∙ cong₂ _+_
          ( rearrangeFourFactors
              left-numerator right-denominator
              left-inverse right-inverse
          ∙ cong
              ((left-numerator · left-inverse) ·_)
              right-law
          ∙ mulIdR
              (left-numerator · left-inverse)
          )
          ( cong
              ((right-numerator · left-denominator) ·_)
              (mulComm left-inverse right-inverse)
          ∙ rearrangeFourFactors
              right-numerator left-denominator
              right-inverse left-inverse
          ∙ cong
              ((right-numerator · right-inverse) ·_)
              left-law
          ∙ mulIdR
              (right-numerator · right-inverse)
          )

combinedDenominator :
  (left-denominator right-denominator : ℝ → ℝ) →
  ℝ → ℝ
combinedDenominator left-denominator right-denominator x =
  left-denominator x · right-denominator x

combinedDenominatorDerivative :
  (left-denominator right-denominator
   left-denominator-derivative right-denominator-derivative : ℝ → ℝ) →
  ℝ → ℝ
combinedDenominatorDerivative
  left-denominator right-denominator
  left-denominator-derivative right-denominator-derivative x =
    left-denominator-derivative x · right-denominator x
      + left-denominator x · right-denominator-derivative x

combinedDenominatorHasDerivative :
  ∀ left-denominator right-denominator
    left-denominator-derivative right-denominator-derivative →
  IsDerivative
    left-denominator left-denominator-derivative →
  IsDerivative
    right-denominator right-denominator-derivative →
  IsDerivative
    (combinedDenominator
      left-denominator right-denominator)
    (combinedDenominatorDerivative
      left-denominator right-denominator
      left-denominator-derivative right-denominator-derivative)
combinedDenominatorHasDerivative
  left-denominator right-denominator
  left-denominator-derivative right-denominator-derivative =
    mulHasDerivative
      left-denominator right-denominator
      left-denominator-derivative right-denominator-derivative

commonDomainToCombinedDenominatorDomain :
  ∀ left-denominator right-denominator →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ApartDenominatorDomain
    (combinedDenominator
      left-denominator right-denominator)
commonDomainToCombinedDenominatorDomain
  left-denominator right-denominator point =
    fst point
    , apartMul
        (left-denominator (fst point))
        (right-denominator (fst point))
        (fst (snd point))
        (snd (snd point))

commonDomainToCombinedDenominatorDomainNE :
  ∀ left-denominator right-denominator →
  NE[
    CommonApartDenominatorDomainPremetricSpace
      left-denominator right-denominator
    ,
    ApartDenominatorDomainPremetricSpace
      (combinedDenominator
        left-denominator right-denominator)
    ]
fst
  (commonDomainToCombinedDenominatorDomainNE
    left-denominator right-denominator) =
      commonDomainToCombinedDenominatorDomain
        left-denominator right-denominator
IsNonExpanding.pres≈
  (snd
    (commonDomainToCombinedDenominatorDomainNE
      left-denominator right-denominator))
  point other ε =
    idfun _

addCombinedNumerator :
  (left-numerator left-denominator
   right-numerator right-denominator : ℝ → ℝ) →
  ℝ → ℝ
addCombinedNumerator
  left-numerator left-denominator
  right-numerator right-denominator x =
    left-numerator x · right-denominator x
      + right-numerator x · left-denominator x

addCombinedNumeratorDerivative :
  (left-numerator left-denominator
   right-numerator right-denominator
   left-numerator-derivative left-denominator-derivative
   right-numerator-derivative right-denominator-derivative : ℝ → ℝ) →
  ℝ → ℝ
addCombinedNumeratorDerivative
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative x =
    ( left-numerator-derivative x · right-denominator x
        + left-numerator x · right-denominator-derivative x
    )
    +
    ( right-numerator-derivative x · left-denominator x
        + right-numerator x · left-denominator-derivative x
    )

addCombinedNumeratorHasDerivative :
  ∀ left-numerator left-denominator
    right-numerator right-denominator
    left-numerator-derivative left-denominator-derivative
    right-numerator-derivative right-denominator-derivative →
  IsDerivative
    left-numerator left-numerator-derivative →
  IsDerivative
    left-denominator left-denominator-derivative →
  IsDerivative
    right-numerator right-numerator-derivative →
  IsDerivative
    right-denominator right-denominator-derivative →
  IsDerivative
    (addCombinedNumerator
      left-numerator left-denominator
      right-numerator right-denominator)
    (addCombinedNumeratorDerivative
      left-numerator left-denominator
      right-numerator right-denominator
      left-numerator-derivative left-denominator-derivative
      right-numerator-derivative right-denominator-derivative)
addCombinedNumeratorHasDerivative
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative
  left-numerator-has-derivative
  left-denominator-has-derivative
  right-numerator-has-derivative
  right-denominator-has-derivative =
    addHasDerivative
      (λ x →
        left-numerator x · right-denominator x)
      (λ x →
        right-numerator x · left-denominator x)
      (λ x →
        left-numerator-derivative x · right-denominator x
          + left-numerator x · right-denominator-derivative x)
      (λ x →
        right-numerator-derivative x · left-denominator x
          + right-numerator x · left-denominator-derivative x)
      (mulHasDerivative
        left-numerator right-denominator
        left-numerator-derivative right-denominator-derivative
        left-numerator-has-derivative
        right-denominator-has-derivative)
      (mulHasDerivative
        right-numerator left-denominator
        right-numerator-derivative left-denominator-derivative
        right-numerator-has-derivative
        left-denominator-has-derivative)

addRationalFunctionsByCombinedDenominatorOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
addRationalFunctionsByCombinedDenominatorOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator point =
    divideOnApartDenominatorDomain
      (addCombinedNumerator
        left-numerator left-denominator
        right-numerator right-denominator)
      (combinedDenominator
        left-denominator right-denominator)
      (commonDomainToCombinedDenominatorDomain
        left-denominator right-denominator point)

addRationalFunctionsByCombinedDenominatorDerivativeOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator
   left-numerator-derivative left-denominator-derivative
   right-numerator-derivative right-denominator-derivative : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
addRationalFunctionsByCombinedDenominatorDerivativeOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative point =
    divideOnApartDenominatorDomainConventionalDerivative
      (addCombinedNumerator
        left-numerator left-denominator
        right-numerator right-denominator)
      (combinedDenominator
        left-denominator right-denominator)
      (addCombinedNumeratorDerivative
        left-numerator left-denominator
        right-numerator right-denominator
        left-numerator-derivative left-denominator-derivative
        right-numerator-derivative right-denominator-derivative)
      (combinedDenominatorDerivative
        left-denominator right-denominator
        left-denominator-derivative right-denominator-derivative)
      (commonDomainToCombinedDenominatorDomain
        left-denominator right-denominator point)

addRationalFunctionsByCombinedDenominatorHasDerivativeAlong :
  ∀ left-numerator left-denominator
    right-numerator right-denominator
    left-numerator-derivative left-denominator-derivative
    right-numerator-derivative right-denominator-derivative →
  IsDerivative
    left-numerator left-numerator-derivative →
  IsDerivative
    left-denominator left-denominator-derivative →
  IsDerivative
    right-numerator right-numerator-derivative →
  IsDerivative
    right-denominator right-denominator-derivative →
  IsDerivativeAlong
    (snd
      (CommonApartDenominatorDomainPremetricSpace
        left-denominator right-denominator))
    commonApartDenominatorDomainCoordinate
    (addRationalFunctionsByCombinedDenominatorOnCommonDomain
      left-numerator left-denominator
      right-numerator right-denominator)
    (addRationalFunctionsByCombinedDenominatorDerivativeOnCommonDomain
      left-numerator left-denominator
      right-numerator right-denominator
      left-numerator-derivative left-denominator-derivative
      right-numerator-derivative right-denominator-derivative)
addRationalFunctionsByCombinedDenominatorHasDerivativeAlong
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative
  left-numerator-has-derivative
  left-denominator-has-derivative
  right-numerator-has-derivative
  right-denominator-has-derivative =
    pullbackHasDerivativeAlong
      (snd
        (CommonApartDenominatorDomainPremetricSpace
          left-denominator right-denominator))
      (snd
        (ApartDenominatorDomainPremetricSpace
          (combinedDenominator
            left-denominator right-denominator)))
      apartDenominatorDomainCoordinate
      (divideOnApartDenominatorDomain
        (addCombinedNumerator
          left-numerator left-denominator
          right-numerator right-denominator)
        (combinedDenominator
          left-denominator right-denominator))
      (divideOnApartDenominatorDomainConventionalDerivative
        (addCombinedNumerator
          left-numerator left-denominator
          right-numerator right-denominator)
        (combinedDenominator
          left-denominator right-denominator)
        (addCombinedNumeratorDerivative
          left-numerator left-denominator
          right-numerator right-denominator
          left-numerator-derivative left-denominator-derivative
          right-numerator-derivative right-denominator-derivative)
        (combinedDenominatorDerivative
          left-denominator right-denominator
          left-denominator-derivative right-denominator-derivative))
      (commonDomainToCombinedDenominatorDomain
        left-denominator right-denominator)
      (snd
        (NE→C
          (commonDomainToCombinedDenominatorDomainNE
            left-denominator right-denominator)))
      (divideOnApartDenominatorDomainHasConventionalDerivativeAlong
        (addCombinedNumerator
          left-numerator left-denominator
          right-numerator right-denominator)
        (combinedDenominator
          left-denominator right-denominator)
        (addCombinedNumeratorDerivative
          left-numerator left-denominator
          right-numerator right-denominator
          left-numerator-derivative left-denominator-derivative
          right-numerator-derivative right-denominator-derivative)
        (combinedDenominatorDerivative
          left-denominator right-denominator
          left-denominator-derivative right-denominator-derivative)
        (addCombinedNumeratorHasDerivative
          left-numerator left-denominator
          right-numerator right-denominator
          left-numerator-derivative left-denominator-derivative
          right-numerator-derivative right-denominator-derivative
          left-numerator-has-derivative
          left-denominator-has-derivative
          right-numerator-has-derivative
          right-denominator-has-derivative)
        (combinedDenominatorHasDerivative
          left-denominator right-denominator
          left-denominator-derivative right-denominator-derivative
          left-denominator-has-derivative
          right-denominator-has-derivative))

addRationalFunctionsByCombinedDenominator≡OnCommonDomain :
  ∀ left-numerator left-denominator
    right-numerator right-denominator point →
  addRationalFunctionsByCombinedDenominatorOnCommonDomain
      left-numerator left-denominator
      right-numerator right-denominator point
    ≡
  addRationalFunctionsOnCommonDomain
    left-numerator left-denominator
    right-numerator right-denominator point
addRationalFunctionsByCombinedDenominator≡OnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator point =
    cong
      (addCombinedNumerator
        left-numerator left-denominator
        right-numerator right-denominator x ·_)
      (inverseℝMul
        (left-denominator x)
        (right-denominator x)
        left-apart right-apart)
    ∙ addFractionsAlgebra
        (left-numerator x) (left-denominator x)
        (right-numerator x) (right-denominator x)
        (inverseℝ (left-denominator x) left-apart)
        (inverseℝ (right-denominator x) right-apart)
        (inverseℝLaw (left-denominator x) left-apart)
        (inverseℝLaw (right-denominator x) right-apart)
  where
  x : ℝ
  x = fst point

  left-apart : 0 ＃ left-denominator x
  left-apart = fst (snd point)

  right-apart : 0 ＃ right-denominator x
  right-apart = snd (snd point)

multiplyCombinedNumerator :
  (left-numerator right-numerator : ℝ → ℝ) →
  ℝ → ℝ
multiplyCombinedNumerator left-numerator right-numerator x =
  left-numerator x · right-numerator x

multiplyCombinedNumeratorDerivative :
  (left-numerator right-numerator
   left-numerator-derivative right-numerator-derivative : ℝ → ℝ) →
  ℝ → ℝ
multiplyCombinedNumeratorDerivative
  left-numerator right-numerator
  left-numerator-derivative right-numerator-derivative x =
    left-numerator-derivative x · right-numerator x
      + left-numerator x · right-numerator-derivative x

multiplyCombinedNumeratorHasDerivative :
  ∀ left-numerator right-numerator
    left-numerator-derivative right-numerator-derivative →
  IsDerivative
    left-numerator left-numerator-derivative →
  IsDerivative
    right-numerator right-numerator-derivative →
  IsDerivative
    (multiplyCombinedNumerator
      left-numerator right-numerator)
    (multiplyCombinedNumeratorDerivative
      left-numerator right-numerator
      left-numerator-derivative right-numerator-derivative)
multiplyCombinedNumeratorHasDerivative
  left-numerator right-numerator
  left-numerator-derivative right-numerator-derivative =
    mulHasDerivative
      left-numerator right-numerator
      left-numerator-derivative right-numerator-derivative

multiplyRationalFunctionsByCombinedDenominatorOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
multiplyRationalFunctionsByCombinedDenominatorOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator point =
    divideOnApartDenominatorDomain
      (multiplyCombinedNumerator
        left-numerator right-numerator)
      (combinedDenominator
        left-denominator right-denominator)
      (commonDomainToCombinedDenominatorDomain
        left-denominator right-denominator point)

multiplyRationalFunctionsByCombinedDenominatorDerivativeOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator
   left-numerator-derivative left-denominator-derivative
   right-numerator-derivative right-denominator-derivative : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
multiplyRationalFunctionsByCombinedDenominatorDerivativeOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative point =
    divideOnApartDenominatorDomainConventionalDerivative
      (multiplyCombinedNumerator
        left-numerator right-numerator)
      (combinedDenominator
        left-denominator right-denominator)
      (multiplyCombinedNumeratorDerivative
        left-numerator right-numerator
        left-numerator-derivative right-numerator-derivative)
      (combinedDenominatorDerivative
        left-denominator right-denominator
        left-denominator-derivative right-denominator-derivative)
      (commonDomainToCombinedDenominatorDomain
        left-denominator right-denominator point)

multiplyRationalFunctionsByCombinedDenominatorHasDerivativeAlong :
  ∀ left-numerator left-denominator
    right-numerator right-denominator
    left-numerator-derivative left-denominator-derivative
    right-numerator-derivative right-denominator-derivative →
  IsDerivative
    left-numerator left-numerator-derivative →
  IsDerivative
    left-denominator left-denominator-derivative →
  IsDerivative
    right-numerator right-numerator-derivative →
  IsDerivative
    right-denominator right-denominator-derivative →
  IsDerivativeAlong
    (snd
      (CommonApartDenominatorDomainPremetricSpace
        left-denominator right-denominator))
    commonApartDenominatorDomainCoordinate
    (multiplyRationalFunctionsByCombinedDenominatorOnCommonDomain
      left-numerator left-denominator
      right-numerator right-denominator)
    (multiplyRationalFunctionsByCombinedDenominatorDerivativeOnCommonDomain
      left-numerator left-denominator
      right-numerator right-denominator
      left-numerator-derivative left-denominator-derivative
      right-numerator-derivative right-denominator-derivative)
multiplyRationalFunctionsByCombinedDenominatorHasDerivativeAlong
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative
  left-numerator-has-derivative
  left-denominator-has-derivative
  right-numerator-has-derivative
  right-denominator-has-derivative =
    pullbackHasDerivativeAlong
      (snd
        (CommonApartDenominatorDomainPremetricSpace
          left-denominator right-denominator))
      (snd
        (ApartDenominatorDomainPremetricSpace
          (combinedDenominator
            left-denominator right-denominator)))
      apartDenominatorDomainCoordinate
      (divideOnApartDenominatorDomain
        (multiplyCombinedNumerator
          left-numerator right-numerator)
        (combinedDenominator
          left-denominator right-denominator))
      (divideOnApartDenominatorDomainConventionalDerivative
        (multiplyCombinedNumerator
          left-numerator right-numerator)
        (combinedDenominator
          left-denominator right-denominator)
        (multiplyCombinedNumeratorDerivative
          left-numerator right-numerator
          left-numerator-derivative right-numerator-derivative)
        (combinedDenominatorDerivative
          left-denominator right-denominator
          left-denominator-derivative right-denominator-derivative))
      (commonDomainToCombinedDenominatorDomain
        left-denominator right-denominator)
      (snd
        (NE→C
          (commonDomainToCombinedDenominatorDomainNE
            left-denominator right-denominator)))
      (divideOnApartDenominatorDomainHasConventionalDerivativeAlong
        (multiplyCombinedNumerator
          left-numerator right-numerator)
        (combinedDenominator
          left-denominator right-denominator)
        (multiplyCombinedNumeratorDerivative
          left-numerator right-numerator
          left-numerator-derivative right-numerator-derivative)
        (combinedDenominatorDerivative
          left-denominator right-denominator
          left-denominator-derivative right-denominator-derivative)
        (multiplyCombinedNumeratorHasDerivative
          left-numerator right-numerator
          left-numerator-derivative right-numerator-derivative
          left-numerator-has-derivative
          right-numerator-has-derivative)
        (combinedDenominatorHasDerivative
          left-denominator right-denominator
          left-denominator-derivative right-denominator-derivative
          left-denominator-has-derivative
          right-denominator-has-derivative))

multiplyRationalFunctionsByCombinedDenominator≡OnCommonDomain :
  ∀ left-numerator left-denominator
    right-numerator right-denominator point →
  multiplyRationalFunctionsByCombinedDenominatorOnCommonDomain
      left-numerator left-denominator
      right-numerator right-denominator point
    ≡
  multiplyRationalFunctionsOnCommonDomain
    left-numerator left-denominator
    right-numerator right-denominator point
multiplyRationalFunctionsByCombinedDenominator≡OnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator point =
    cong
      (multiplyCombinedNumerator
        left-numerator right-numerator x ·_)
      (inverseℝMul
        (left-denominator x)
        (right-denominator x)
        left-apart right-apart)
    ∙ rearrangeFourFactors
        (left-numerator x) (right-numerator x)
        (inverseℝ (left-denominator x) left-apart)
        (inverseℝ (right-denominator x) right-apart)
  where
  x : ℝ
  x = fst point

  left-apart : 0 ＃ left-denominator x
  left-apart = fst (snd point)

  right-apart : 0 ＃ right-denominator x
  right-apart = snd (snd point)

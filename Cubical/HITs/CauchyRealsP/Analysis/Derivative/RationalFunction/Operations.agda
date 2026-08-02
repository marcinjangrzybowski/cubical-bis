module Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Algebra
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Domain
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.NormalForm

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace

CommonApartDenominatorPredicate :
  (left-denominator right-denominator : ℝ → ℝ) →
  ℙ ℝ
CommonApartDenominatorPredicate
  left-denominator right-denominator x =
    ( (0 ＃ left-denominator x)
    × (0 ＃ right-denominator x)
    )
    , isProp×
        (isProp＃ 0 (left-denominator x))
        (isProp＃ 0 (right-denominator x))

CommonApartDenominatorDomain :
  (ℝ → ℝ) → (ℝ → ℝ) → Type
CommonApartDenominatorDomain
  left-denominator right-denominator =
    Σ[ x ∈ ℝ ]
      x ∈ CommonApartDenominatorPredicate
        left-denominator right-denominator

CommonApartDenominatorDomainPremetricSpace :
  (left-denominator right-denominator : ℝ → ℝ) →
  PremetricSpace ℓ-zero ℓ-zero
CommonApartDenominatorDomainPremetricSpace
  left-denominator right-denominator =
    PremetricSubspace
      ℝPremetricSpace
      (CommonApartDenominatorPredicate
        left-denominator right-denominator)

commonApartDenominatorDomainCoordinate :
  ∀ {left-denominator right-denominator} →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
commonApartDenominatorDomainCoordinate =
  fst

commonApartDenominatorDomainCoordinateIsContinuous :
  ∀ left-denominator right-denominator →
  isContinuous
    (snd
      (CommonApartDenominatorDomainPremetricSpace
        left-denominator right-denominator))
    commonApartDenominatorDomainCoordinate
    (snd ℝPremetricSpace)
commonApartDenominatorDomainCoordinateIsContinuous
  left-denominator right-denominator =
    snd
      (NE→C
        (subspaceInclusionNE
          ℝPremetricSpace
          (CommonApartDenominatorPredicate
            left-denominator right-denominator)))

commonApartDenominatorDomainLeft :
  ∀ left-denominator right-denominator →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ApartDenominatorDomain left-denominator
commonApartDenominatorDomainLeft
  left-denominator right-denominator point =
    fst point , fst (snd point)

commonApartDenominatorDomainRight :
  ∀ left-denominator right-denominator →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ApartDenominatorDomain right-denominator
commonApartDenominatorDomainRight
  left-denominator right-denominator point =
    fst point , snd (snd point)

commonApartDenominatorDomainLeftNE :
  ∀ left-denominator right-denominator →
  NE[
    CommonApartDenominatorDomainPremetricSpace
      left-denominator right-denominator
    ,
    ApartDenominatorDomainPremetricSpace
      left-denominator
    ]
fst
  (commonApartDenominatorDomainLeftNE
    left-denominator right-denominator) =
      commonApartDenominatorDomainLeft
        left-denominator right-denominator
IsNonExpanding.pres≈
  (snd
    (commonApartDenominatorDomainLeftNE
      left-denominator right-denominator))
  point other ε =
    idfun _

commonApartDenominatorDomainRightNE :
  ∀ left-denominator right-denominator →
  NE[
    CommonApartDenominatorDomainPremetricSpace
      left-denominator right-denominator
    ,
    ApartDenominatorDomainPremetricSpace
      right-denominator
    ]
fst
  (commonApartDenominatorDomainRightNE
    left-denominator right-denominator) =
      commonApartDenominatorDomainRight
        left-denominator right-denominator
IsNonExpanding.pres≈
  (snd
    (commonApartDenominatorDomainRightNE
      left-denominator right-denominator))
  point other ε =
    idfun _

leftRationalFunctionOnCommonDomain :
  (left-numerator left-denominator right-denominator : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
leftRationalFunctionOnCommonDomain
  left-numerator left-denominator right-denominator point =
    divideOnApartDenominatorDomain
      left-numerator left-denominator
      (commonApartDenominatorDomainLeft
        left-denominator right-denominator point)

leftRationalFunctionDerivativeOnCommonDomain :
  (left-numerator left-denominator
   right-denominator
   left-numerator-derivative
   left-denominator-derivative : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
leftRationalFunctionDerivativeOnCommonDomain
  left-numerator left-denominator right-denominator
  left-numerator-derivative
  left-denominator-derivative point =
    divideOnApartDenominatorDomainConventionalDerivative
      left-numerator left-denominator
      left-numerator-derivative
      left-denominator-derivative
      (commonApartDenominatorDomainLeft
        left-denominator right-denominator point)

leftRationalFunctionOnCommonDomainHasDerivativeAlong :
  ∀ left-numerator left-denominator right-denominator
    left-numerator-derivative left-denominator-derivative →
  IsDerivative
    left-numerator left-numerator-derivative →
  IsDerivative
    left-denominator left-denominator-derivative →
  IsDerivativeAlong
    (snd
      (CommonApartDenominatorDomainPremetricSpace
        left-denominator right-denominator))
    commonApartDenominatorDomainCoordinate
    (leftRationalFunctionOnCommonDomain
      left-numerator left-denominator right-denominator)
    (leftRationalFunctionDerivativeOnCommonDomain
      left-numerator left-denominator right-denominator
      left-numerator-derivative
      left-denominator-derivative)
leftRationalFunctionOnCommonDomainHasDerivativeAlong
  left-numerator left-denominator right-denominator
  left-numerator-derivative left-denominator-derivative
  left-numerator-has-derivative
  left-denominator-has-derivative =
    pullbackHasDerivativeAlong
      (snd
        (CommonApartDenominatorDomainPremetricSpace
          left-denominator right-denominator))
      (snd
        (ApartDenominatorDomainPremetricSpace
          left-denominator))
      apartDenominatorDomainCoordinate
      (divideOnApartDenominatorDomain
        left-numerator left-denominator)
      (divideOnApartDenominatorDomainConventionalDerivative
        left-numerator left-denominator
        left-numerator-derivative
        left-denominator-derivative)
      (commonApartDenominatorDomainLeft
        left-denominator right-denominator)
      (snd
        (NE→C
          (commonApartDenominatorDomainLeftNE
            left-denominator right-denominator)))
      (divideOnApartDenominatorDomainHasConventionalDerivativeAlong
        left-numerator left-denominator
        left-numerator-derivative
        left-denominator-derivative
        left-numerator-has-derivative
        left-denominator-has-derivative)

rightRationalFunctionOnCommonDomain :
  (right-numerator left-denominator right-denominator : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
rightRationalFunctionOnCommonDomain
  right-numerator left-denominator right-denominator point =
    divideOnApartDenominatorDomain
      right-numerator right-denominator
      (commonApartDenominatorDomainRight
        left-denominator right-denominator point)

rightRationalFunctionDerivativeOnCommonDomain :
  (right-numerator left-denominator
   right-denominator
   right-numerator-derivative
   right-denominator-derivative : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
rightRationalFunctionDerivativeOnCommonDomain
  right-numerator left-denominator right-denominator
  right-numerator-derivative
  right-denominator-derivative point =
    divideOnApartDenominatorDomainConventionalDerivative
      right-numerator right-denominator
      right-numerator-derivative
      right-denominator-derivative
      (commonApartDenominatorDomainRight
        left-denominator right-denominator point)

rightRationalFunctionOnCommonDomainHasDerivativeAlong :
  ∀ right-numerator left-denominator right-denominator
    right-numerator-derivative right-denominator-derivative →
  IsDerivative
    right-numerator right-numerator-derivative →
  IsDerivative
    right-denominator right-denominator-derivative →
  IsDerivativeAlong
    (snd
      (CommonApartDenominatorDomainPremetricSpace
        left-denominator right-denominator))
    commonApartDenominatorDomainCoordinate
    (rightRationalFunctionOnCommonDomain
      right-numerator left-denominator right-denominator)
    (rightRationalFunctionDerivativeOnCommonDomain
      right-numerator left-denominator right-denominator
      right-numerator-derivative
      right-denominator-derivative)
rightRationalFunctionOnCommonDomainHasDerivativeAlong
  right-numerator left-denominator right-denominator
  right-numerator-derivative right-denominator-derivative
  right-numerator-has-derivative
  right-denominator-has-derivative =
    pullbackHasDerivativeAlong
      (snd
        (CommonApartDenominatorDomainPremetricSpace
          left-denominator right-denominator))
      (snd
        (ApartDenominatorDomainPremetricSpace
          right-denominator))
      apartDenominatorDomainCoordinate
      (divideOnApartDenominatorDomain
        right-numerator right-denominator)
      (divideOnApartDenominatorDomainConventionalDerivative
        right-numerator right-denominator
        right-numerator-derivative
        right-denominator-derivative)
      (commonApartDenominatorDomainRight
        left-denominator right-denominator)
      (snd
        (NE→C
          (commonApartDenominatorDomainRightNE
            left-denominator right-denominator)))
      (divideOnApartDenominatorDomainHasConventionalDerivativeAlong
        right-numerator right-denominator
        right-numerator-derivative
        right-denominator-derivative
        right-numerator-has-derivative
        right-denominator-has-derivative)

addRationalFunctionsOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
addRationalFunctionsOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator point =
    leftRationalFunctionOnCommonDomain
        left-numerator left-denominator
        right-denominator point
    + rightRationalFunctionOnCommonDomain
        right-numerator left-denominator
        right-denominator point

addRationalFunctionsDerivativeOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator
   left-numerator-derivative left-denominator-derivative
   right-numerator-derivative right-denominator-derivative : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
addRationalFunctionsDerivativeOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative point =
    leftRationalFunctionDerivativeOnCommonDomain
      left-numerator left-denominator right-denominator
      left-numerator-derivative left-denominator-derivative
      point
    + rightRationalFunctionDerivativeOnCommonDomain
      right-numerator left-denominator right-denominator
      right-numerator-derivative right-denominator-derivative
      point

addRationalFunctionsOnCommonDomainHasDerivativeAlong :
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
    (addRationalFunctionsOnCommonDomain
      left-numerator left-denominator
      right-numerator right-denominator)
    (addRationalFunctionsDerivativeOnCommonDomain
      left-numerator left-denominator
      right-numerator right-denominator
      left-numerator-derivative left-denominator-derivative
      right-numerator-derivative right-denominator-derivative)
addRationalFunctionsOnCommonDomainHasDerivativeAlong
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative
  left-numerator-has-derivative
  left-denominator-has-derivative
  right-numerator-has-derivative
  right-denominator-has-derivative =
    addHasDerivativeAlong
      (snd
        (CommonApartDenominatorDomainPremetricSpace
          left-denominator right-denominator))
      commonApartDenominatorDomainCoordinate
      (leftRationalFunctionOnCommonDomain
        left-numerator left-denominator right-denominator)
      (rightRationalFunctionOnCommonDomain
        right-numerator left-denominator right-denominator)
      (leftRationalFunctionDerivativeOnCommonDomain
        left-numerator left-denominator right-denominator
        left-numerator-derivative left-denominator-derivative)
      (rightRationalFunctionDerivativeOnCommonDomain
        right-numerator left-denominator right-denominator
        right-numerator-derivative right-denominator-derivative)
      (leftRationalFunctionOnCommonDomainHasDerivativeAlong
        left-numerator left-denominator right-denominator
        left-numerator-derivative left-denominator-derivative
        left-numerator-has-derivative
        left-denominator-has-derivative)
      (rightRationalFunctionOnCommonDomainHasDerivativeAlong
        right-numerator left-denominator right-denominator
        right-numerator-derivative right-denominator-derivative
        right-numerator-has-derivative
        right-denominator-has-derivative)

multiplyRationalFunctionsOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
multiplyRationalFunctionsOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator point =
    leftRationalFunctionOnCommonDomain
        left-numerator left-denominator
        right-denominator point
    · rightRationalFunctionOnCommonDomain
        right-numerator left-denominator
        right-denominator point

multiplyRationalFunctionsDerivativeOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator
   left-numerator-derivative left-denominator-derivative
   right-numerator-derivative right-denominator-derivative : ℝ → ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator
    →
  ℝ
multiplyRationalFunctionsDerivativeOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative point =
    left-value-derivative point · right-value point
      + left-value point · right-value-derivative point
  where
  left-value =
    leftRationalFunctionOnCommonDomain
      left-numerator left-denominator right-denominator

  right-value =
    rightRationalFunctionOnCommonDomain
      right-numerator left-denominator right-denominator

  left-value-derivative =
    leftRationalFunctionDerivativeOnCommonDomain
      left-numerator left-denominator right-denominator
      left-numerator-derivative left-denominator-derivative

  right-value-derivative =
    rightRationalFunctionDerivativeOnCommonDomain
      right-numerator left-denominator right-denominator
      right-numerator-derivative right-denominator-derivative

multiplyRationalFunctionsOnCommonDomainHasDerivativeAlong :
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
    (multiplyRationalFunctionsOnCommonDomain
      left-numerator left-denominator
      right-numerator right-denominator)
    (multiplyRationalFunctionsDerivativeOnCommonDomain
      left-numerator left-denominator
      right-numerator right-denominator
      left-numerator-derivative left-denominator-derivative
      right-numerator-derivative right-denominator-derivative)
multiplyRationalFunctionsOnCommonDomainHasDerivativeAlong
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative
  left-numerator-has-derivative
  left-denominator-has-derivative
  right-numerator-has-derivative
  right-denominator-has-derivative =
    mulHasDerivativeAlong
      (snd
        (CommonApartDenominatorDomainPremetricSpace
          left-denominator right-denominator))
      commonApartDenominatorDomainCoordinate
      (leftRationalFunctionOnCommonDomain
        left-numerator left-denominator right-denominator)
      (rightRationalFunctionOnCommonDomain
        right-numerator left-denominator right-denominator)
      (leftRationalFunctionDerivativeOnCommonDomain
        left-numerator left-denominator right-denominator
        left-numerator-derivative left-denominator-derivative)
      (rightRationalFunctionDerivativeOnCommonDomain
        right-numerator left-denominator right-denominator
        right-numerator-derivative right-denominator-derivative)
      (commonApartDenominatorDomainCoordinateIsContinuous
        left-denominator right-denominator)
      (leftRationalFunctionOnCommonDomainHasDerivativeAlong
        left-numerator left-denominator right-denominator
        left-numerator-derivative left-denominator-derivative
        left-numerator-has-derivative
        left-denominator-has-derivative)
      (rightRationalFunctionOnCommonDomainHasDerivativeAlong
        right-numerator left-denominator right-denominator
        right-numerator-derivative right-denominator-derivative
        right-numerator-has-derivative
        right-denominator-has-derivative)

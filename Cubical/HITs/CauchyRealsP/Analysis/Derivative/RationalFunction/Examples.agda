module Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Basic
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Quotient
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Domain
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.NormalForm
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Composition

open import Cubical.Relation.Premetric.Mappings

shiftedDenominator : ℝ → ℝ → ℝ
shiftedDenominator centre x = x - centre

shiftedDenominatorDerivative : ℝ → ℝ → ℝ
shiftedDenominatorDerivative centre x = 1 - 0

shiftedDenominatorHasDerivative : ∀ centre →
  IsDerivative
    (shiftedDenominator centre)
    (shiftedDenominatorDerivative centre)
shiftedDenominatorHasDerivative centre =
  subHasDerivative
    (idfun ℝ) (const centre)
    (const 1) (const 0)
    identityHasDerivative
    (constantHasDerivative centre)

ShiftedReciprocalDomain : ℝ → Type
ShiftedReciprocalDomain centre =
  ApartDenominatorDomain
    (shiftedDenominator centre)

shiftedReciprocalDomainPoint :
  ∀ centre x →
  x ＃ centre →
  ShiftedReciprocalDomain centre
shiftedReciprocalDomainPoint centre x x-apart-centre =
  x , apart→zeroApartDifference
        x centre x-apart-centre

shiftedReciprocalOnDomain :
  ∀ centre →
  ShiftedReciprocalDomain centre → ℝ
shiftedReciprocalOnDomain centre =
  divideOnApartDenominatorDomain
    (const 1) (shiftedDenominator centre)

shiftedReciprocalOnDomainDerivative :
  ∀ centre →
  ShiftedReciprocalDomain centre → ℝ
shiftedReciprocalOnDomainDerivative centre =
  divideOnApartDenominatorDomainConventionalDerivative
    (const 1) (shiftedDenominator centre)
    (const 0) (shiftedDenominatorDerivative centre)

shiftedReciprocalOnDomainHasDerivativeAlong :
  ∀ centre →
  IsDerivativeAlong
    (snd
      (ApartDenominatorDomainPremetricSpace
        (shiftedDenominator centre)))
    apartDenominatorDomainCoordinate
    (shiftedReciprocalOnDomain centre)
    (shiftedReciprocalOnDomainDerivative centre)
shiftedReciprocalOnDomainHasDerivativeAlong centre =
  divideOnApartDenominatorDomainHasConventionalDerivativeAlong
    (const 1) (shiftedDenominator centre)
    (const 0) (shiftedDenominatorDerivative centre)
    (constantHasDerivative 1)
    (shiftedDenominatorHasDerivative centre)

twoPoleDenominator : ℝ → ℝ → ℝ → ℝ
twoPoleDenominator left-pole right-pole x =
  shiftedDenominator left-pole x
    · shiftedDenominator right-pole x

twoPoleDenominatorDerivative :
  ℝ → ℝ → ℝ → ℝ
twoPoleDenominatorDerivative left-pole right-pole x =
  shiftedDenominatorDerivative left-pole x
      · shiftedDenominator right-pole x
    + shiftedDenominator left-pole x
      · shiftedDenominatorDerivative right-pole x

twoPoleDenominatorHasDerivative : ∀ left-pole right-pole →
  IsDerivative
    (twoPoleDenominator left-pole right-pole)
    (twoPoleDenominatorDerivative left-pole right-pole)
twoPoleDenominatorHasDerivative left-pole right-pole =
  mulHasDerivative
    (shiftedDenominator left-pole)
    (shiftedDenominator right-pole)
    (shiftedDenominatorDerivative left-pole)
    (shiftedDenominatorDerivative right-pole)
    (shiftedDenominatorHasDerivative left-pole)
    (shiftedDenominatorHasDerivative right-pole)

TwoPoleRationalDomain : ℝ → ℝ → Type
TwoPoleRationalDomain left-pole right-pole =
  ApartDenominatorDomain
    (twoPoleDenominator left-pole right-pole)

swapTwoPoleRationalDomain :
  ∀ left-pole right-pole →
  TwoPoleRationalDomain left-pole right-pole →
  TwoPoleRationalDomain right-pole left-pole
swapTwoPoleRationalDomain
  left-pole right-pole =
    mapApartDenominatorDomainByPath
      (twoPoleDenominator left-pole right-pole)
      (twoPoleDenominator right-pole left-pole)
      (λ x →
        mulComm
          (shiftedDenominator left-pole x)
          (shiftedDenominator right-pole x))

swapTwoPoleRationalDomainNE :
  ∀ left-pole right-pole →
  NE[
    ApartDenominatorDomainPremetricSpace
      (twoPoleDenominator left-pole right-pole)
    ,
    ApartDenominatorDomainPremetricSpace
      (twoPoleDenominator right-pole left-pole)
    ]
swapTwoPoleRationalDomainNE
  left-pole right-pole =
    mapApartDenominatorDomainByPathNE
      (twoPoleDenominator left-pole right-pole)
      (twoPoleDenominator right-pole left-pole)
      (λ x →
        mulComm
          (shiftedDenominator left-pole x)
          (shiftedDenominator right-pole x))

swapTwoPoleRationalDomain-involutive :
  ∀ left-pole right-pole point →
  swapTwoPoleRationalDomain
      right-pole left-pole
      (swapTwoPoleRationalDomain
        left-pole right-pole point)
    ≡
  point
swapTwoPoleRationalDomain-involutive
  left-pole right-pole point =
    Σ≡Prop
      (λ x →
        isProp＃ 0
          (twoPoleDenominator
            left-pole right-pole x))
      refl

twoPoleRationalDomainPoint :
  ∀ left-pole right-pole x →
  x ＃ left-pole →
  x ＃ right-pole →
  TwoPoleRationalDomain left-pole right-pole
twoPoleRationalDomainPoint
  left-pole right-pole x
  x-apart-left x-apart-right =
    x
    , apartMul
        (shiftedDenominator left-pole x)
        (shiftedDenominator right-pole x)
        (apart→zeroApartDifference
          x left-pole x-apart-left)
        (apart→zeroApartDifference
          x right-pole x-apart-right)

twoPoleRational :
  ∀ left-pole right-pole →
  TwoPoleRationalDomain left-pole right-pole → ℝ
twoPoleRational left-pole right-pole =
  divideOnApartDenominatorDomain
    (idfun ℝ)
    (twoPoleDenominator left-pole right-pole)

twoPoleRationalDerivative :
  ∀ left-pole right-pole →
  TwoPoleRationalDomain left-pole right-pole → ℝ
twoPoleRationalDerivative left-pole right-pole =
  divideOnApartDenominatorDomainConventionalDerivative
    (idfun ℝ)
    (twoPoleDenominator left-pole right-pole)
    (const 1)
    (twoPoleDenominatorDerivative left-pole right-pole)

twoPoleRationalHasDerivativeAlong :
  ∀ left-pole right-pole →
  IsDerivativeAlong
    (snd
      (ApartDenominatorDomainPremetricSpace
        (twoPoleDenominator left-pole right-pole)))
    apartDenominatorDomainCoordinate
    (twoPoleRational left-pole right-pole)
    (twoPoleRationalDerivative left-pole right-pole)
twoPoleRationalHasDerivativeAlong left-pole right-pole =
  divideOnApartDenominatorDomainHasConventionalDerivativeAlong
    (idfun ℝ)
    (twoPoleDenominator left-pole right-pole)
    (const 1)
    (twoPoleDenominatorDerivative left-pole right-pole)
    identityHasDerivative
    (twoPoleDenominatorHasDerivative left-pole right-pole)

-- Applying reciprocal twice is a small but genuine consumer of the
-- composition domain: the first shifted reciprocal supplies the second
-- denominator, and its apartness follows constructively from signed
-- reciprocal apartness.
DoubleReciprocalCompositionDomain : ℝ → Type
DoubleReciprocalCompositionDomain centre =
  RationalCompositionDomain
    (const 1)
    (shiftedDenominator centre)
    (idfun ℝ)

doubleReciprocalCompositionDomainPoint :
  ∀ centre →
  ShiftedReciprocalDomain centre →
  DoubleReciprocalCompositionDomain centre
doubleReciprocalCompositionDomainPoint centre point =
  point
  , apartMul
      1
      (inverseℝ
        (shiftedDenominator centre (fst point))
        (snd point))
      apartOne
      (inverseℝApart
        (shiftedDenominator centre (fst point))
        (snd point))

doubleReciprocalComposition :
  ∀ centre →
  DoubleReciprocalCompositionDomain centre → ℝ
doubleReciprocalComposition centre =
  composeRationalFunctionsOnNaturalDomain
    (const 1)
    (shiftedDenominator centre)
    (const 1)
    (idfun ℝ)

doubleReciprocalCompositionDerivative :
  ∀ centre →
  DoubleReciprocalCompositionDomain centre → ℝ
doubleReciprocalCompositionDerivative centre =
  composeRationalFunctionsDerivativeOnNaturalDomain
    (const 1)
    (shiftedDenominator centre)
    (const 1)
    (idfun ℝ)
    (const 0)
    (shiftedDenominatorDerivative centre)
    (const 0)
    (const 1)

doubleReciprocalCompositionHasDerivativeAlong :
  ∀ centre →
  IsDerivativeAlong
    (snd
      (RationalCompositionDomainPremetricSpace
        (const 1)
        (shiftedDenominator centre)
        (idfun ℝ)))
    (rationalCompositionDomainCoordinate
      (const 1)
      (shiftedDenominator centre)
      (idfun ℝ))
    (doubleReciprocalComposition centre)
    (doubleReciprocalCompositionDerivative centre)
doubleReciprocalCompositionHasDerivativeAlong centre =
  composeRationalFunctionsOnNaturalDomainHasDerivativeAlong
    (const 1)
    (shiftedDenominator centre)
    (const 1)
    (idfun ℝ)
    (const 0)
    (shiftedDenominatorDerivative centre)
    (const 0)
    (const 1)
    (constantHasDerivative 1)
    (shiftedDenominatorHasDerivative centre)
    (constantHasDerivative 1)
    identityHasDerivative

doubleReciprocalCompositionValue :
  ∀ centre point →
  doubleReciprocalComposition
      centre
      (doubleReciprocalCompositionDomainPoint centre point)
    ≡
  shiftedDenominator centre (fst point)
doubleReciprocalCompositionValue centre point =
  mulIdL (inverseℝ inner-value inner-apart)
  ∙ sym
      (inverseℝUnique
        inner-value inner-apart
        (shiftedDenominator centre (fst point))
        (mulDivideR
          1
          (shiftedDenominator centre (fst point))
          (snd point)))
  where
  inner-value : ℝ
  inner-value =
    divideℝ
      1
      (shiftedDenominator centre (fst point))
      (snd point)

  inner-apart : 0 ＃ inner-value
  inner-apart =
    snd
      (doubleReciprocalCompositionDomainPoint
        centre point)

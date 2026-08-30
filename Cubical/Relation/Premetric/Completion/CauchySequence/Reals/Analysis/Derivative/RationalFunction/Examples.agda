module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.MultiplicativeApartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Basic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Product
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Composition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Domain


shiftedDenominator : Real.ℝ → Real.ℝ → Real.ℝ
shiftedDenominator centre x =
  x Group.- centre


shiftedDenominatorDerivative : Real.ℝ → Real.ℝ → Real.ℝ
shiftedDenominatorDerivative centre x =
  Real.ιℚ 1 Group.- Real.ιℚ 0


shiftedDenominatorHasDerivative : ∀ centre →
  IsDerivative
    (shiftedDenominator centre)
    (shiftedDenominatorDerivative centre)
shiftedDenominatorHasDerivative centre =
  subHasDerivative
    (idfun Real.ℝ) (λ _ → centre)
    (λ _ → Real.ιℚ 1)
    (λ _ → Real.ιℚ 0)
    identityHasDerivative
    (constantHasDerivative centre)


ShiftedReciprocalDomain : Real.ℝ → Type
ShiftedReciprocalDomain centre =
  ApartDenominatorDomain (shiftedDenominator centre)


shiftedReciprocalDomainPoint :
  ∀ centre x →
  x ＃ centre →
  ShiftedReciprocalDomain centre
shiftedReciprocalDomainPoint centre x x-apart-centre =
  x , apart→zeroApartDifference x centre x-apart-centre


shiftedReciprocalOnDomain :
  ∀ centre → ShiftedReciprocalDomain centre → Real.ℝ
shiftedReciprocalOnDomain centre =
  divideOnApartDenominatorDomain
    (λ _ → Real.ιℚ 1)
    (shiftedDenominator centre)


shiftedReciprocalOnDomainDerivative :
  ∀ centre → ShiftedReciprocalDomain centre → Real.ℝ
shiftedReciprocalOnDomainDerivative centre =
  divideOnApartDenominatorDomainDerivative
    (λ _ → Real.ιℚ 1)
    (shiftedDenominator centre)
    (λ _ → Real.ιℚ 0)
    (shiftedDenominatorDerivative centre)


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
  divideOnApartDenominatorDomainHasDerivativeAlong
    (λ _ → Real.ιℚ 1)
    (shiftedDenominator centre)
    (λ _ → Real.ιℚ 0)
    (shiftedDenominatorDerivative centre)
    (constantHasDerivative (Real.ιℚ 1))
    (shiftedDenominatorHasDerivative centre)


twoPoleDenominator : Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
twoPoleDenominator left-pole right-pole x =
  shiftedDenominator left-pole x Mul.·
    shiftedDenominator right-pole x


twoPoleDenominatorDerivative :
  Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
twoPoleDenominatorDerivative left-pole right-pole x =
  (shiftedDenominatorDerivative left-pole x Mul.·
    shiftedDenominator right-pole x) Add.+
  (shiftedDenominator left-pole x Mul.·
    shiftedDenominatorDerivative right-pole x)


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


TwoPoleRationalDomain : Real.ℝ → Real.ℝ → Type
TwoPoleRationalDomain left-pole right-pole =
  ApartDenominatorDomain
    (twoPoleDenominator left-pole right-pole)


swapTwoPoleRationalDomain :
  ∀ left-pole right-pole →
  TwoPoleRationalDomain left-pole right-pole →
  TwoPoleRationalDomain right-pole left-pole
swapTwoPoleRationalDomain left-pole right-pole =
  mapApartDenominatorDomainByPath
    (twoPoleDenominator left-pole right-pole)
    (twoPoleDenominator right-pole left-pole)
    (λ x →
      mul-comm
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
swapTwoPoleRationalDomainNE left-pole right-pole =
  mapApartDenominatorDomainByPathNE
    (twoPoleDenominator left-pole right-pole)
    (twoPoleDenominator right-pole left-pole)
    (λ x →
      mul-comm
        (shiftedDenominator left-pole x)
        (shiftedDenominator right-pole x))


swapTwoPoleRationalDomain-involutive :
  ∀ left-pole right-pole point →
  swapTwoPoleRationalDomain right-pole left-pole
      (swapTwoPoleRationalDomain
        left-pole right-pole point)
    ≡
  point
swapTwoPoleRationalDomain-involutive
  left-pole right-pole point =
    Σ≡Prop
      (λ x →
        isProp＃ (Real.ιℚ 0)
          (twoPoleDenominator left-pole right-pole x))
      refl


twoPoleRationalDomainPoint :
  ∀ left-pole right-pole x →
  x ＃ left-pole →
  x ＃ right-pole →
  TwoPoleRationalDomain left-pole right-pole
twoPoleRationalDomainPoint
  left-pole right-pole x x-apart-left x-apart-right =
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
  TwoPoleRationalDomain left-pole right-pole → Real.ℝ
twoPoleRational left-pole right-pole =
  divideOnApartDenominatorDomain
    (idfun Real.ℝ)
    (twoPoleDenominator left-pole right-pole)


twoPoleRationalDerivative :
  ∀ left-pole right-pole →
  TwoPoleRationalDomain left-pole right-pole → Real.ℝ
twoPoleRationalDerivative left-pole right-pole =
  divideOnApartDenominatorDomainDerivative
    (idfun Real.ℝ)
    (twoPoleDenominator left-pole right-pole)
    (λ _ → Real.ιℚ 1)
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
  divideOnApartDenominatorDomainHasDerivativeAlong
    (idfun Real.ℝ)
    (twoPoleDenominator left-pole right-pole)
    (λ _ → Real.ιℚ 1)
    (twoPoleDenominatorDerivative left-pole right-pole)
    identityHasDerivative
    (twoPoleDenominatorHasDerivative left-pole right-pole)


-- Applying reciprocal twice is a genuine dependent-domain composition.
-- The value theorem confirms that the witness-rich construction computes
-- extensionally as expected.

DoubleReciprocalCompositionDomain : Real.ℝ → Type
DoubleReciprocalCompositionDomain centre =
  RationalCompositionDomain
    (λ _ → Real.ιℚ 1)
    (shiftedDenominator centre)
    (idfun Real.ℝ)


doubleReciprocalCompositionDomainPoint :
  ∀ centre →
  ShiftedReciprocalDomain centre →
  DoubleReciprocalCompositionDomain centre
doubleReciprocalCompositionDomainPoint centre point =
  point
  , apartMul
      (Real.ιℚ 1)
      (inverseℝ
        (shiftedDenominator centre (fst point))
        (snd point))
      apartOne
      (inverseℝApart
        (shiftedDenominator centre (fst point))
        (snd point))


doubleReciprocalComposition :
  ∀ centre → DoubleReciprocalCompositionDomain centre → Real.ℝ
doubleReciprocalComposition centre =
  composeRationalFunctionsOnNaturalDomain
    (λ _ → Real.ιℚ 1)
    (shiftedDenominator centre)
    (λ _ → Real.ιℚ 1)
    (idfun Real.ℝ)


doubleReciprocalCompositionDerivative :
  ∀ centre → DoubleReciprocalCompositionDomain centre → Real.ℝ
doubleReciprocalCompositionDerivative centre =
  composeRationalFunctionsDerivativeOnNaturalDomain
    (λ _ → Real.ιℚ 1)
    (shiftedDenominator centre)
    (λ _ → Real.ιℚ 1)
    (idfun Real.ℝ)
    (λ _ → Real.ιℚ 0)
    (shiftedDenominatorDerivative centre)
    (λ _ → Real.ιℚ 0)
    (λ _ → Real.ιℚ 1)


doubleReciprocalCompositionHasDerivativeAlong :
  ∀ centre →
  IsDerivativeAlong
    (snd
      (RationalCompositionDomainPremetricSpace
        (λ _ → Real.ιℚ 1)
        (shiftedDenominator centre)
        (idfun Real.ℝ)))
    (rationalCompositionDomainCoordinate
      (λ _ → Real.ιℚ 1)
      (shiftedDenominator centre)
      (idfun Real.ℝ))
    (doubleReciprocalComposition centre)
    (doubleReciprocalCompositionDerivative centre)
doubleReciprocalCompositionHasDerivativeAlong centre =
  composeRationalFunctionsOnNaturalDomainHasDerivativeAlong
    (λ _ → Real.ιℚ 1)
    (shiftedDenominator centre)
    (λ _ → Real.ιℚ 1)
    (idfun Real.ℝ)
    (λ _ → Real.ιℚ 0)
    (shiftedDenominatorDerivative centre)
    (λ _ → Real.ιℚ 0)
    (λ _ → Real.ιℚ 1)
    (constantHasDerivative (Real.ιℚ 1))
    (shiftedDenominatorHasDerivative centre)
    (constantHasDerivative (Real.ιℚ 1))
    identityHasDerivative


doubleReciprocalCompositionValue :
  ∀ centre point →
  doubleReciprocalComposition centre
      (doubleReciprocalCompositionDomainPoint centre point)
    ≡
  shiftedDenominator centre (fst point)
doubleReciprocalCompositionValue centre point =
    mul-one-left (inverseℝ inner-value inner-apart)
  ∙ sym
      (inverseℝUnique
        inner-value inner-apart
        (shiftedDenominator centre (fst point))
        (mulDivideRight
          (Real.ιℚ 1)
          (shiftedDenominator centre (fst point))
          (snd point)))
  where
  inner-value : Real.ℝ
  inner-value =
    divideℝ
      (Real.ιℚ 1)
      (shiftedDenominator centre (fst point))
      (snd point)

  inner-apart : Real.ιℚ 0 ＃ inner-value
  inner-apart =
    snd (doubleReciprocalCompositionDomainPoint centre point)

module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.OpenSubspace
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Product
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Domain


-- Binary rational operations live on the intersection of the two natural
-- denominator domains.  Both apartness components are propositions, so this
-- common domain still has exactly the same metric as its real coordinate.

CommonApartDenominatorPredicate :
  (left-denominator right-denominator : Real.ℝ → Real.ℝ) →
  ℙ Real.ℝ
CommonApartDenominatorPredicate
  left-denominator right-denominator x =
    ( (Real.ιℚ 0 ＃ left-denominator x)
    × (Real.ιℚ 0 ＃ right-denominator x)
    )
    , isProp×
        (isProp＃ (Real.ιℚ 0) (left-denominator x))
        (isProp＃ (Real.ιℚ 0) (right-denominator x))


CommonApartDenominatorDomain :
  (Real.ℝ → Real.ℝ) → (Real.ℝ → Real.ℝ) → Type
CommonApartDenominatorDomain
  left-denominator right-denominator =
    Σ[ x ∈ Real.ℝ ]
      x ∈ CommonApartDenominatorPredicate
        left-denominator right-denominator


CommonApartDenominatorDomainPremetricSpace :
  (left-denominator right-denominator : Real.ℝ → Real.ℝ) →
  PremetricSpace ℓ-zero ℓ-zero
CommonApartDenominatorDomainPremetricSpace
  left-denominator right-denominator =
    PremetricSubspace
      Real.ℝPremetricSpace
      (CommonApartDenominatorPredicate
        left-denominator right-denominator)


commonApartDenominatorDomainCoordinate :
  ∀ {left-denominator right-denominator} →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
commonApartDenominatorDomainCoordinate = fst


commonApartDenominatorDomainCoordinateIsContinuous :
  ∀ left-denominator right-denominator →
  isContinuous
    (snd
      (CommonApartDenominatorDomainPremetricSpace
        left-denominator right-denominator))
    commonApartDenominatorDomainCoordinate
    (snd Real.ℝPremetricSpace)
commonApartDenominatorDomainCoordinateIsContinuous
  left-denominator right-denominator =
    snd
      (NE→C
        (subspaceInclusionNE
          Real.ℝPremetricSpace
          (CommonApartDenominatorPredicate
            left-denominator right-denominator)))


commonApartDenominatorPredicateIsOpen :
  ∀ left-denominator right-denominator →
  isContinuous
    (snd Real.ℝPremetricSpace) left-denominator
    (snd Real.ℝPremetricSpace) →
  isContinuous
    (snd Real.ℝPremetricSpace) right-denominator
    (snd Real.ℝPremetricSpace) →
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    (CommonApartDenominatorPredicate
      left-denominator right-denominator)
commonApartDenominatorPredicateIsOpen
  left-denominator right-denominator
  left-continuous right-continuous =
    intersectionIsOpen
      (snd Real.ℝPremetricSpace)
      (ApartDenominatorPredicate left-denominator)
      (ApartDenominatorPredicate right-denominator)
      (apartDenominatorPredicateIsOpen
        left-denominator left-continuous)
      (apartDenominatorPredicateIsOpen
        right-denominator right-continuous)


commonApartDenominatorPredicateOfDerivativesIsOpen :
  ∀ left-denominator right-denominator
    left-denominator-derivative right-denominator-derivative →
  IsDerivative left-denominator left-denominator-derivative →
  IsDerivative right-denominator right-denominator-derivative →
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    (CommonApartDenominatorPredicate
      left-denominator right-denominator)
commonApartDenominatorPredicateOfDerivativesIsOpen
  left-denominator right-denominator
  left-denominator-derivative right-denominator-derivative
  left-has-derivative right-has-derivative =
    commonApartDenominatorPredicateIsOpen
      left-denominator right-denominator
      (derivativeIsContinuous
        left-denominator left-denominator-derivative
        left-has-derivative)
      (derivativeIsContinuous
        right-denominator right-denominator-derivative
        right-has-derivative)


-- This generic bridge applies to every operation constructed below.  The
-- relative function need not itself be presented as a quotient: once its
-- derivative along the common coordinate is known, openness of the two
-- denominator loci is enough to recover the ordinary derivative of any
-- agreeing ambient extension.

commonApartDenominatorDerivativeAtWithExtension :
  ∀ left-denominator right-denominator
    left-denominator-derivative right-denominator-derivative
    relative-function relative-derivative extension →
  IsDerivative left-denominator left-denominator-derivative →
  IsDerivative right-denominator right-denominator-derivative →
  IsDerivativeAlong
    (snd
      (CommonApartDenominatorDomainPremetricSpace
        left-denominator right-denominator))
    commonApartDenominatorDomainCoordinate
    relative-function relative-derivative →
  (∀ point →
    extension (fst point) ≡ relative-function point) →
  ∀ x →
  (left-apart : Real.ιℚ 0 ＃ left-denominator x) →
  (right-apart : Real.ιℚ 0 ＃ right-denominator x) →
  IsDerivativeAt
    extension
    (relative-derivative (x , left-apart , right-apart))
    x
commonApartDenominatorDerivativeAtWithExtension
  left-denominator right-denominator
  left-denominator-derivative right-denominator-derivative
  relative-function relative-derivative extension
  left-has-derivative right-has-derivative
  relative-has-derivative agrees x left-apart right-apart =
    openSubspaceDerivativeAtWithExtension
      (CommonApartDenominatorPredicate
        left-denominator right-denominator)
      (commonApartDenominatorPredicateOfDerivativesIsOpen
        left-denominator right-denominator
        left-denominator-derivative right-denominator-derivative
        left-has-derivative right-has-derivative)
      relative-function relative-derivative extension
      relative-has-derivative agrees
      x (left-apart , right-apart)


commonApartDenominatorDomainLeft :
  ∀ left-denominator right-denominator →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  ApartDenominatorDomain left-denominator
commonApartDenominatorDomainLeft
  left-denominator right-denominator point =
    fst point , fst (snd point)


commonApartDenominatorDomainRight :
  ∀ left-denominator right-denominator →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
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
    ApartDenominatorDomainPremetricSpace left-denominator
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
    ApartDenominatorDomainPremetricSpace right-denominator
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
  (left-numerator left-denominator right-denominator :
    Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
leftRationalFunctionOnCommonDomain
  left-numerator left-denominator right-denominator point =
    divideOnApartDenominatorDomain
      left-numerator left-denominator
      (commonApartDenominatorDomainLeft
        left-denominator right-denominator point)


leftRationalFunctionDerivativeOnCommonDomain :
  (left-numerator left-denominator right-denominator
   left-numerator-derivative left-denominator-derivative :
    Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
leftRationalFunctionDerivativeOnCommonDomain
  left-numerator left-denominator right-denominator
  left-numerator-derivative left-denominator-derivative point =
    divideOnApartDenominatorDomainDerivative
      left-numerator left-denominator
      left-numerator-derivative left-denominator-derivative
      (commonApartDenominatorDomainLeft
        left-denominator right-denominator point)


leftRationalFunctionOnCommonDomainHasDerivativeAlong :
  ∀ left-numerator left-denominator right-denominator
    left-numerator-derivative left-denominator-derivative →
  IsDerivative left-numerator left-numerator-derivative →
  IsDerivative left-denominator left-denominator-derivative →
  IsDerivativeAlong
    (snd
      (CommonApartDenominatorDomainPremetricSpace
        left-denominator right-denominator))
    commonApartDenominatorDomainCoordinate
    (leftRationalFunctionOnCommonDomain
      left-numerator left-denominator right-denominator)
    (leftRationalFunctionDerivativeOnCommonDomain
      left-numerator left-denominator right-denominator
      left-numerator-derivative left-denominator-derivative)
leftRationalFunctionOnCommonDomainHasDerivativeAlong
  left-numerator left-denominator right-denominator
  left-numerator-derivative left-denominator-derivative
  left-numerator-has-derivative left-denominator-has-derivative =
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
      (divideOnApartDenominatorDomainDerivative
        left-numerator left-denominator
        left-numerator-derivative left-denominator-derivative)
      (commonApartDenominatorDomainLeft
        left-denominator right-denominator)
      (snd
        (NE→C
          (commonApartDenominatorDomainLeftNE
            left-denominator right-denominator)))
      (divideOnApartDenominatorDomainHasDerivativeAlong
        left-numerator left-denominator
        left-numerator-derivative left-denominator-derivative
        left-numerator-has-derivative
        left-denominator-has-derivative)


rightRationalFunctionOnCommonDomain :
  (right-numerator left-denominator right-denominator :
    Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
rightRationalFunctionOnCommonDomain
  right-numerator left-denominator right-denominator point =
    divideOnApartDenominatorDomain
      right-numerator right-denominator
      (commonApartDenominatorDomainRight
        left-denominator right-denominator point)


rightRationalFunctionDerivativeOnCommonDomain :
  (right-numerator left-denominator right-denominator
   right-numerator-derivative right-denominator-derivative :
    Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
rightRationalFunctionDerivativeOnCommonDomain
  right-numerator left-denominator right-denominator
  right-numerator-derivative right-denominator-derivative point =
    divideOnApartDenominatorDomainDerivative
      right-numerator right-denominator
      right-numerator-derivative right-denominator-derivative
      (commonApartDenominatorDomainRight
        left-denominator right-denominator point)


rightRationalFunctionOnCommonDomainHasDerivativeAlong :
  ∀ right-numerator left-denominator right-denominator
    right-numerator-derivative right-denominator-derivative →
  IsDerivative right-numerator right-numerator-derivative →
  IsDerivative right-denominator right-denominator-derivative →
  IsDerivativeAlong
    (snd
      (CommonApartDenominatorDomainPremetricSpace
        left-denominator right-denominator))
    commonApartDenominatorDomainCoordinate
    (rightRationalFunctionOnCommonDomain
      right-numerator left-denominator right-denominator)
    (rightRationalFunctionDerivativeOnCommonDomain
      right-numerator left-denominator right-denominator
      right-numerator-derivative right-denominator-derivative)
rightRationalFunctionOnCommonDomainHasDerivativeAlong
  right-numerator left-denominator right-denominator
  right-numerator-derivative right-denominator-derivative
  right-numerator-has-derivative right-denominator-has-derivative =
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
      (divideOnApartDenominatorDomainDerivative
        right-numerator right-denominator
        right-numerator-derivative right-denominator-derivative)
      (commonApartDenominatorDomainRight
        left-denominator right-denominator)
      (snd
        (NE→C
          (commonApartDenominatorDomainRightNE
            left-denominator right-denominator)))
      (divideOnApartDenominatorDomainHasDerivativeAlong
        right-numerator right-denominator
        right-numerator-derivative right-denominator-derivative
        right-numerator-has-derivative
        right-denominator-has-derivative)


addRationalFunctionsOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator : Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
addRationalFunctionsOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator point =
    leftRationalFunctionOnCommonDomain
        left-numerator left-denominator right-denominator point
    Add.+
    rightRationalFunctionOnCommonDomain
        right-numerator left-denominator right-denominator point


addRationalFunctionsDerivativeOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator
   left-numerator-derivative left-denominator-derivative
   right-numerator-derivative right-denominator-derivative :
    Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
addRationalFunctionsDerivativeOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative point =
    leftRationalFunctionDerivativeOnCommonDomain
      left-numerator left-denominator right-denominator
      left-numerator-derivative left-denominator-derivative point
    Add.+
    rightRationalFunctionDerivativeOnCommonDomain
      right-numerator left-denominator right-denominator
      right-numerator-derivative right-denominator-derivative point


addRationalFunctionsOnCommonDomainHasDerivativeAlong :
  ∀ left-numerator left-denominator
    right-numerator right-denominator
    left-numerator-derivative left-denominator-derivative
    right-numerator-derivative right-denominator-derivative →
  IsDerivative left-numerator left-numerator-derivative →
  IsDerivative left-denominator left-denominator-derivative →
  IsDerivative right-numerator right-numerator-derivative →
  IsDerivative right-denominator right-denominator-derivative →
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
  left-numerator-has-derivative left-denominator-has-derivative
  right-numerator-has-derivative right-denominator-has-derivative =
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
   right-numerator right-denominator : Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
multiplyRationalFunctionsOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator point =
    leftRationalFunctionOnCommonDomain
        left-numerator left-denominator right-denominator point
    Mul.·
    rightRationalFunctionOnCommonDomain
        right-numerator left-denominator right-denominator point


multiplyRationalFunctionsDerivativeOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator
   left-numerator-derivative left-denominator-derivative
   right-numerator-derivative right-denominator-derivative :
    Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
multiplyRationalFunctionsDerivativeOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative point =
    (left-value-derivative point Mul.· right-value point) Add.+
      (left-value point Mul.· right-value-derivative point)
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
  IsDerivative left-numerator left-numerator-derivative →
  IsDerivative left-denominator left-denominator-derivative →
  IsDerivative right-numerator right-numerator-derivative →
  IsDerivative right-denominator right-denominator-derivative →
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
  left-numerator-has-derivative left-denominator-has-derivative
  right-numerator-has-derivative right-denominator-has-derivative =
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

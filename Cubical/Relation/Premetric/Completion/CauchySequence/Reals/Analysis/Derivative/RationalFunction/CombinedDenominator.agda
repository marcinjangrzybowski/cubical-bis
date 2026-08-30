module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.CombinedDenominator where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Tactics.CommRingSolver

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.MultiplicativeApartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Product
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Domain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Operations


private
  module AbstractCombinedDenominator {ℓR} (R : CommRing ℓR) where
    open CommRingStr (snd R)

    rearrange : ∀ a b c d →
      (a · b) · (c · d) ≡ (a · c) · (b · d)
    rearrange a b c d = solve! R

    addFractions :
      ∀ left-numerator left-denominator
        right-numerator right-denominator
        left-inverse right-inverse →
      left-denominator · left-inverse ≡ 1r →
      right-denominator · right-inverse ≡ 1r →
      ((left-numerator · right-denominator) +
          (right-numerator · left-denominator)) ·
          (left-inverse · right-inverse)
        ≡
      (left-numerator · left-inverse) +
        (right-numerator · right-inverse)
    addFractions
      left-numerator left-denominator
      right-numerator right-denominator
      left-inverse right-inverse left-law right-law =
        ·DistL+
          (left-numerator · right-denominator)
          (right-numerator · left-denominator)
          (left-inverse · right-inverse)
      ∙ cong₂ _+_
          ( rearrange
              left-numerator right-denominator
              left-inverse right-inverse
          ∙ cong
              ((left-numerator · left-inverse) ·_)
              right-law
          ∙ ·IdR (left-numerator · left-inverse)
          )
          ( cong
              ((right-numerator · left-denominator) ·_)
              (·Comm left-inverse right-inverse)
          ∙ rearrange
              right-numerator left-denominator
              right-inverse left-inverse
          ∙ cong
              ((right-numerator · right-inverse) ·_)
              left-law
          ∙ ·IdR (right-numerator · right-inverse)
          )


combinedDenominator :
  (left-denominator right-denominator : Real.ℝ → Real.ℝ) →
  Real.ℝ → Real.ℝ
combinedDenominator left-denominator right-denominator x =
  left-denominator x Mul.· right-denominator x


combinedDenominatorDerivative :
  (left-denominator right-denominator
   left-denominator-derivative right-denominator-derivative :
    Real.ℝ → Real.ℝ) →
  Real.ℝ → Real.ℝ
combinedDenominatorDerivative
  left-denominator right-denominator
  left-denominator-derivative right-denominator-derivative x =
    (left-denominator-derivative x Mul.· right-denominator x) Add.+
      (left-denominator x Mul.· right-denominator-derivative x)


combinedDenominatorHasDerivative :
  ∀ left-denominator right-denominator
    left-denominator-derivative right-denominator-derivative →
  IsDerivative left-denominator left-denominator-derivative →
  IsDerivative right-denominator right-denominator-derivative →
  IsDerivative
    (combinedDenominator left-denominator right-denominator)
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
      left-denominator right-denominator →
  ApartDenominatorDomain
    (combinedDenominator left-denominator right-denominator)
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
      (combinedDenominator left-denominator right-denominator)
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


-- A generic single-quotient consumer factors out all subspace transport.
-- Addition and multiplication below differ only in their combined
-- numerators.

quotientByCombinedDenominatorOnCommonDomain :
  (combined-numerator left-denominator right-denominator :
    Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
quotientByCombinedDenominatorOnCommonDomain
  combined-numerator left-denominator right-denominator point =
    divideOnApartDenominatorDomain
      combined-numerator
      (combinedDenominator left-denominator right-denominator)
      (commonDomainToCombinedDenominatorDomain
        left-denominator right-denominator point)


quotientByCombinedDenominatorDerivativeOnCommonDomain :
  (combined-numerator left-denominator right-denominator
   combined-numerator-derivative
   left-denominator-derivative right-denominator-derivative :
    Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
quotientByCombinedDenominatorDerivativeOnCommonDomain
  combined-numerator left-denominator right-denominator
  combined-numerator-derivative
  left-denominator-derivative right-denominator-derivative point =
    divideOnApartDenominatorDomainDerivative
      combined-numerator
      (combinedDenominator left-denominator right-denominator)
      combined-numerator-derivative
      (combinedDenominatorDerivative
        left-denominator right-denominator
        left-denominator-derivative right-denominator-derivative)
      (commonDomainToCombinedDenominatorDomain
        left-denominator right-denominator point)


quotientByCombinedDenominatorHasDerivativeAlong :
  ∀ combined-numerator left-denominator right-denominator
    combined-numerator-derivative
    left-denominator-derivative right-denominator-derivative →
  IsDerivative combined-numerator combined-numerator-derivative →
  IsDerivative left-denominator left-denominator-derivative →
  IsDerivative right-denominator right-denominator-derivative →
  IsDerivativeAlong
    (snd
      (CommonApartDenominatorDomainPremetricSpace
        left-denominator right-denominator))
    commonApartDenominatorDomainCoordinate
    (quotientByCombinedDenominatorOnCommonDomain
      combined-numerator left-denominator right-denominator)
    (quotientByCombinedDenominatorDerivativeOnCommonDomain
      combined-numerator left-denominator right-denominator
      combined-numerator-derivative
      left-denominator-derivative right-denominator-derivative)
quotientByCombinedDenominatorHasDerivativeAlong
  combined-numerator left-denominator right-denominator
  combined-numerator-derivative
  left-denominator-derivative right-denominator-derivative
  combined-numerator-has-derivative
  left-denominator-has-derivative
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
        combined-numerator
        (combinedDenominator left-denominator right-denominator))
      (divideOnApartDenominatorDomainDerivative
        combined-numerator
        (combinedDenominator left-denominator right-denominator)
        combined-numerator-derivative
        (combinedDenominatorDerivative
          left-denominator right-denominator
          left-denominator-derivative right-denominator-derivative))
      (commonDomainToCombinedDenominatorDomain
        left-denominator right-denominator)
      (snd
        (NE→C
          (commonDomainToCombinedDenominatorDomainNE
            left-denominator right-denominator)))
      (divideOnApartDenominatorDomainHasDerivativeAlong
        combined-numerator
        (combinedDenominator left-denominator right-denominator)
        combined-numerator-derivative
        (combinedDenominatorDerivative
          left-denominator right-denominator
          left-denominator-derivative right-denominator-derivative)
        combined-numerator-has-derivative
        (combinedDenominatorHasDerivative
          left-denominator right-denominator
          left-denominator-derivative right-denominator-derivative
          left-denominator-has-derivative
          right-denominator-has-derivative))


addCombinedNumerator :
  (left-numerator left-denominator
   right-numerator right-denominator : Real.ℝ → Real.ℝ) →
  Real.ℝ → Real.ℝ
addCombinedNumerator
  left-numerator left-denominator
  right-numerator right-denominator x =
    (left-numerator x Mul.· right-denominator x) Add.+
      (right-numerator x Mul.· left-denominator x)


addCombinedNumeratorDerivative :
  (left-numerator left-denominator
   right-numerator right-denominator
   left-numerator-derivative left-denominator-derivative
   right-numerator-derivative right-denominator-derivative :
    Real.ℝ → Real.ℝ) →
  Real.ℝ → Real.ℝ
addCombinedNumeratorDerivative
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative x =
    ((left-numerator-derivative x Mul.· right-denominator x) Add.+
      (left-numerator x Mul.· right-denominator-derivative x)) Add.+
    ((right-numerator-derivative x Mul.· left-denominator x) Add.+
      (right-numerator x Mul.· left-denominator-derivative x))


addCombinedNumeratorHasDerivative :
  ∀ left-numerator left-denominator
    right-numerator right-denominator
    left-numerator-derivative left-denominator-derivative
    right-numerator-derivative right-denominator-derivative →
  IsDerivative left-numerator left-numerator-derivative →
  IsDerivative left-denominator left-denominator-derivative →
  IsDerivative right-numerator right-numerator-derivative →
  IsDerivative right-denominator right-denominator-derivative →
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
  left-numerator-has-derivative left-denominator-has-derivative
  right-numerator-has-derivative right-denominator-has-derivative =
    addHasDerivative
      (λ x → left-numerator x Mul.· right-denominator x)
      (λ x → right-numerator x Mul.· left-denominator x)
      (λ x →
        (left-numerator-derivative x Mul.· right-denominator x) Add.+
          (left-numerator x Mul.· right-denominator-derivative x))
      (λ x →
        (right-numerator-derivative x Mul.· left-denominator x) Add.+
          (right-numerator x Mul.· left-denominator-derivative x))
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
   right-numerator right-denominator : Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
addRationalFunctionsByCombinedDenominatorOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator =
    quotientByCombinedDenominatorOnCommonDomain
      (addCombinedNumerator
        left-numerator left-denominator
        right-numerator right-denominator)
      left-denominator right-denominator


addRationalFunctionsByCombinedDenominatorDerivativeOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator
   left-numerator-derivative left-denominator-derivative
   right-numerator-derivative right-denominator-derivative :
    Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
addRationalFunctionsByCombinedDenominatorDerivativeOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative =
    quotientByCombinedDenominatorDerivativeOnCommonDomain
      (addCombinedNumerator
        left-numerator left-denominator
        right-numerator right-denominator)
      left-denominator right-denominator
      (addCombinedNumeratorDerivative
        left-numerator left-denominator
        right-numerator right-denominator
        left-numerator-derivative left-denominator-derivative
        right-numerator-derivative right-denominator-derivative)
      left-denominator-derivative right-denominator-derivative


addRationalFunctionsByCombinedDenominatorHasDerivativeAlong :
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
  left-numerator-has-derivative left-denominator-has-derivative
  right-numerator-has-derivative right-denominator-has-derivative =
    quotientByCombinedDenominatorHasDerivativeAlong
      (addCombinedNumerator
        left-numerator left-denominator
        right-numerator right-denominator)
      left-denominator right-denominator
      (addCombinedNumeratorDerivative
        left-numerator left-denominator
        right-numerator right-denominator
        left-numerator-derivative left-denominator-derivative
        right-numerator-derivative right-denominator-derivative)
      left-denominator-derivative right-denominator-derivative
      (addCombinedNumeratorHasDerivative
        left-numerator left-denominator
        right-numerator right-denominator
        left-numerator-derivative left-denominator-derivative
        right-numerator-derivative right-denominator-derivative
        left-numerator-has-derivative
        left-denominator-has-derivative
        right-numerator-has-derivative
        right-denominator-has-derivative)
      left-denominator-has-derivative
      right-denominator-has-derivative


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
        right-numerator right-denominator x Mul.·_)
      (inverseℝMul
        (left-denominator x) (right-denominator x)
        left-apart right-apart)
    ∙ AbstractCombinedDenominator.addFractions
        ℝCommRing
        (left-numerator x) (left-denominator x)
        (right-numerator x) (right-denominator x)
        (inverseℝ (left-denominator x) left-apart)
        (inverseℝ (right-denominator x) right-apart)
        (inverseℝLaw (left-denominator x) left-apart)
        (inverseℝLaw (right-denominator x) right-apart)
  where
  x : Real.ℝ
  x = fst point

  left-apart = fst (snd point)
  right-apart = snd (snd point)


multiplyCombinedNumerator :
  (left-numerator right-numerator : Real.ℝ → Real.ℝ) →
  Real.ℝ → Real.ℝ
multiplyCombinedNumerator left-numerator right-numerator x =
  left-numerator x Mul.· right-numerator x


multiplyCombinedNumeratorDerivative :
  (left-numerator right-numerator
   left-numerator-derivative right-numerator-derivative :
    Real.ℝ → Real.ℝ) →
  Real.ℝ → Real.ℝ
multiplyCombinedNumeratorDerivative
  left-numerator right-numerator
  left-numerator-derivative right-numerator-derivative x =
    (left-numerator-derivative x Mul.· right-numerator x) Add.+
      (left-numerator x Mul.· right-numerator-derivative x)


multiplyCombinedNumeratorHasDerivative :
  ∀ left-numerator right-numerator
    left-numerator-derivative right-numerator-derivative →
  IsDerivative left-numerator left-numerator-derivative →
  IsDerivative right-numerator right-numerator-derivative →
  IsDerivative
    (multiplyCombinedNumerator left-numerator right-numerator)
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
   right-numerator right-denominator : Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
multiplyRationalFunctionsByCombinedDenominatorOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator =
    quotientByCombinedDenominatorOnCommonDomain
      (multiplyCombinedNumerator left-numerator right-numerator)
      left-denominator right-denominator


multiplyRationalFunctionsByCombinedDenominatorDerivativeOnCommonDomain :
  (left-numerator left-denominator
   right-numerator right-denominator
   left-numerator-derivative left-denominator-derivative
   right-numerator-derivative right-denominator-derivative :
    Real.ℝ → Real.ℝ) →
  CommonApartDenominatorDomain
      left-denominator right-denominator →
  Real.ℝ
multiplyRationalFunctionsByCombinedDenominatorDerivativeOnCommonDomain
  left-numerator left-denominator
  right-numerator right-denominator
  left-numerator-derivative left-denominator-derivative
  right-numerator-derivative right-denominator-derivative =
    quotientByCombinedDenominatorDerivativeOnCommonDomain
      (multiplyCombinedNumerator left-numerator right-numerator)
      left-denominator right-denominator
      (multiplyCombinedNumeratorDerivative
        left-numerator right-numerator
        left-numerator-derivative right-numerator-derivative)
      left-denominator-derivative right-denominator-derivative


multiplyRationalFunctionsByCombinedDenominatorHasDerivativeAlong :
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
  left-numerator-has-derivative left-denominator-has-derivative
  right-numerator-has-derivative right-denominator-has-derivative =
    quotientByCombinedDenominatorHasDerivativeAlong
      (multiplyCombinedNumerator left-numerator right-numerator)
      left-denominator right-denominator
      (multiplyCombinedNumeratorDerivative
        left-numerator right-numerator
        left-numerator-derivative right-numerator-derivative)
      left-denominator-derivative right-denominator-derivative
      (multiplyCombinedNumeratorHasDerivative
        left-numerator right-numerator
        left-numerator-derivative right-numerator-derivative
        left-numerator-has-derivative
        right-numerator-has-derivative)
      left-denominator-has-derivative
      right-denominator-has-derivative


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
        left-numerator right-numerator x Mul.·_)
      (inverseℝMul
        (left-denominator x) (right-denominator x)
        left-apart right-apart)
    ∙ AbstractCombinedDenominator.rearrange
        ℝCommRing
        (left-numerator x) (right-numerator x)
        (inverseℝ (left-denominator x) left-apart)
        (inverseℝ (right-denominator x) right-apart)
  where
  x : Real.ℝ
  x = fst point

  left-apart = fst (snd point)
  right-apart = snd (snd point)

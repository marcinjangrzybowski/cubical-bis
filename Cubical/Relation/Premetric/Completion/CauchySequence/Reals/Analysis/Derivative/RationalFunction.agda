module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List using (List)
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Sum using (inl)

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.Relation.Premetric.OpenPredicate

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.OrderedCommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Polynomial
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Basic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Polynomial
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Product
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Quotient
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Domain public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Uniqueness


private
  module ℝOrder = OrderedCommRingTheory ℝOrderedCommRing


-- Globally defined polynomial quotients are the convenient special case in
-- which the denominator is apart everywhere.  Their derivative uses the
-- normalized quotient rule, avoiding a fresh proof-indexed inverse of the
-- squared denominator.

evaluatePolynomialQuotient :
  (numerator denominator : List Real.ℝ) →
  (∀ x → Real.ιℚ 0 ＃ evaluatePolynomial denominator x) →
  Real.ℝ → Real.ℝ
evaluatePolynomialQuotient
  numerator denominator denominator-apart =
    divideByApartDenominator
      (evaluatePolynomial numerator)
      (evaluatePolynomial denominator)
      denominator-apart


evaluatePolynomialQuotientDerivative :
  (numerator denominator : List Real.ℝ) →
  (denominator-apart :
    ∀ x → Real.ιℚ 0 ＃ evaluatePolynomial denominator x) →
  Real.ℝ → Real.ℝ
evaluatePolynomialQuotientDerivative
  numerator denominator denominator-apart =
    quotientRuleNormalizedDerivative
      (evaluatePolynomial numerator)
      (evaluatePolynomial denominator)
      denominator-apart
      (evaluatePolynomialDerivative numerator)
      (evaluatePolynomialDerivative denominator)


evaluatePolynomialQuotientHasDerivative :
  ∀ numerator denominator denominator-apart →
  IsDerivative
    (evaluatePolynomialQuotient
      numerator denominator denominator-apart)
    (evaluatePolynomialQuotientDerivative
      numerator denominator denominator-apart)
evaluatePolynomialQuotientHasDerivative
  numerator denominator denominator-apart =
    divideByApartDenominatorHasNormalizedDerivative
      (evaluatePolynomial numerator)
      (evaluatePolynomial denominator)
      denominator-apart
      (evaluatePolynomialDerivative numerator)
      (evaluatePolynomialDerivative denominator)
      (evaluatePolynomialHasDerivative numerator)
      (evaluatePolynomialHasDerivative denominator)


evaluatePolynomialQuotientDerivativeUnique :
  ∀ numerator denominator denominator-apart derivative →
  IsDerivative
    (evaluatePolynomialQuotient
      numerator denominator denominator-apart)
    derivative →
  derivative ≡
    evaluatePolynomialQuotientDerivative
      numerator denominator denominator-apart
evaluatePolynomialQuotientDerivativeUnique
  numerator denominator denominator-apart derivative
  has-derivative =
    derivativeFunctionUnique
      (evaluatePolynomialQuotient
        numerator denominator denominator-apart)
      derivative
      (evaluatePolynomialQuotientDerivative
        numerator denominator denominator-apart)
      has-derivative
      (evaluatePolynomialQuotientHasDerivative
        numerator denominator denominator-apart)


-- Without global apartness, the same data gives a partial rational function
-- on the denominator's canonical open locus.

PolynomialQuotientDomain : List Real.ℝ → Type
PolynomialQuotientDomain denominator =
  ApartDenominatorDomain (evaluatePolynomial denominator)


polynomialQuotientDomainIsOpen :
  ∀ denominator →
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    (ApartDenominatorPredicate
      (evaluatePolynomial denominator))
polynomialQuotientDomainIsOpen denominator =
  apartDenominatorPredicateOfDerivativeIsOpen
    (evaluatePolynomial denominator)
    (evaluatePolynomialDerivative denominator)
    (evaluatePolynomialHasDerivative denominator)


evaluatePolynomialQuotientOnDomain :
  (numerator denominator : List Real.ℝ) →
  PolynomialQuotientDomain denominator → Real.ℝ
evaluatePolynomialQuotientOnDomain numerator denominator =
  divideOnApartDenominatorDomain
    (evaluatePolynomial numerator)
    (evaluatePolynomial denominator)


evaluatePolynomialQuotientOnDomainDerivative :
  (numerator denominator : List Real.ℝ) →
  PolynomialQuotientDomain denominator → Real.ℝ
evaluatePolynomialQuotientOnDomainDerivative numerator denominator =
  divideOnApartDenominatorDomainDerivative
    (evaluatePolynomial numerator)
    (evaluatePolynomial denominator)
    (evaluatePolynomialDerivative numerator)
    (evaluatePolynomialDerivative denominator)


evaluatePolynomialQuotientOnDomainHasDerivativeAlong :
  ∀ numerator denominator →
  IsDerivativeAlong
    (snd
      (ApartDenominatorDomainPremetricSpace
        (evaluatePolynomial denominator)))
    apartDenominatorDomainCoordinate
    (evaluatePolynomialQuotientOnDomain numerator denominator)
    (evaluatePolynomialQuotientOnDomainDerivative
      numerator denominator)
evaluatePolynomialQuotientOnDomainHasDerivativeAlong
  numerator denominator =
    divideOnApartDenominatorDomainHasDerivativeAlong
      (evaluatePolynomial numerator)
      (evaluatePolynomial denominator)
      (evaluatePolynomialDerivative numerator)
      (evaluatePolynomialDerivative denominator)
      (evaluatePolynomialHasDerivative numerator)
      (evaluatePolynomialHasDerivative denominator)


evaluatePolynomialQuotientOnDomainDerivativeAtWithExtension :
  ∀ numerator denominator extension →
  (∀ point →
    extension (fst point) ≡
      evaluatePolynomialQuotientOnDomain
        numerator denominator point) →
  ∀ x →
  (x-apart :
    Real.ιℚ 0 ＃ evaluatePolynomial denominator x) →
  IsDerivativeAt
    extension
    (evaluatePolynomialQuotientOnDomainDerivative
      numerator denominator (x , x-apart))
    x
evaluatePolynomialQuotientOnDomainDerivativeAtWithExtension
  numerator denominator extension agrees =
    divideOnApartDenominatorDomainDerivativeAtWithExtension
      (evaluatePolynomial numerator)
      (evaluatePolynomial denominator)
      (evaluatePolynomialDerivative numerator)
      (evaluatePolynomialDerivative denominator)
      extension
      (evaluatePolynomialHasDerivative numerator)
      (evaluatePolynomialHasDerivative denominator)
      agrees


globalPolynomialQuotientPoint :
  ∀ denominator →
  (denominator-apart :
    ∀ x → Real.ιℚ 0 ＃ evaluatePolynomial denominator x) →
  Real.ℝ → PolynomialQuotientDomain denominator
globalPolynomialQuotientPoint denominator denominator-apart x =
  x , denominator-apart x


evaluatePolynomialQuotientOnDomain-global :
  ∀ numerator denominator denominator-apart x →
  evaluatePolynomialQuotientOnDomain numerator denominator
      (globalPolynomialQuotientPoint
        denominator denominator-apart x)
    ≡
  evaluatePolynomialQuotient
    numerator denominator denominator-apart x
evaluatePolynomialQuotientOnDomain-global
  numerator denominator denominator-apart x =
    refl


evaluatePolynomialQuotientOnDomainDerivative-global :
  ∀ numerator denominator denominator-apart x →
  evaluatePolynomialQuotientOnDomainDerivative
      numerator denominator
      (globalPolynomialQuotientPoint
        denominator denominator-apart x)
    ≡
  evaluatePolynomialQuotientDerivative
    numerator denominator denominator-apart x
evaluatePolynomialQuotientOnDomainDerivative-global
  numerator denominator denominator-apart x =
    refl


-- A closed example showing how positivity discharges the global apartness
-- premise.  The derivative is deliberately left in product-rule normal form
-- so it computes without a separate ring-normalization theorem.

onePlusSquare : Real.ℝ → Real.ℝ
onePlusSquare x =
  Real.ιℚ 1 Add.+ (x Mul.· x)


onePlusSquareDerivative : Real.ℝ → Real.ℝ
onePlusSquareDerivative x =
  Real.ιℚ 0 Add.+
    ((Real.ιℚ 1 Mul.· x) Add.+
      (x Mul.· Real.ιℚ 1))


onePlusSquarePositive :
  ∀ x → Real.ιℚ 0 <ℝ onePlusSquare x
onePlusSquarePositive x =
  subst
    (_<ℝ onePlusSquare x)
    (add-zero-left (Real.ιℚ 0))
    (≪≤ℝ-add
      (Real.ιℚ 0) (Real.ιℚ 1)
      (Real.ιℚ 0) (x Mul.· x)
      (isOrderedCommRingℝ .IsOrderedCommRing.0<1)
      (ℝOrder.0≤² x))


onePlusSquareApart :
  ∀ x → Real.ιℚ 0 ＃ onePlusSquare x
onePlusSquareApart x =
  inl (onePlusSquarePositive x)


onePlusSquareHasDerivative :
  IsDerivative onePlusSquare onePlusSquareDerivative
onePlusSquareHasDerivative =
  addHasDerivative
    (λ _ → Real.ιℚ 1)
    (λ x → x Mul.· x)
    (λ _ → Real.ιℚ 0)
    (λ x →
      (Real.ιℚ 1 Mul.· x) Add.+
        (x Mul.· Real.ιℚ 1))
    (constantHasDerivative (Real.ιℚ 1))
    (mulHasDerivative
      (idfun Real.ℝ) (idfun Real.ℝ)
      (λ _ → Real.ιℚ 1)
      (λ _ → Real.ιℚ 1)
      identityHasDerivative identityHasDerivative)


identityOverOnePlusSquare : Real.ℝ → Real.ℝ
identityOverOnePlusSquare =
  divideByApartDenominator
    (idfun Real.ℝ) onePlusSquare onePlusSquareApart


identityOverOnePlusSquareDerivative : Real.ℝ → Real.ℝ
identityOverOnePlusSquareDerivative =
  quotientRuleNormalizedDerivative
    (idfun Real.ℝ) onePlusSquare onePlusSquareApart
    (λ _ → Real.ιℚ 1) onePlusSquareDerivative


identityOverOnePlusSquareHasDerivative :
  IsDerivative
    identityOverOnePlusSquare
    identityOverOnePlusSquareDerivative
identityOverOnePlusSquareHasDerivative =
  divideByApartDenominatorHasNormalizedDerivative
    (idfun Real.ℝ) onePlusSquare onePlusSquareApart
    (λ _ → Real.ιℚ 1) onePlusSquareDerivative
    identityHasDerivative onePlusSquareHasDerivative


open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.NormalForm public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Operations public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Composition public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.CombinedDenominator public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Examples public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.GeometricTail public

module Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List using (List)
open import Cubical.Data.Sum using (inl)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Basic
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Polynomial
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Quotient
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Domain
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.NormalForm
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Uniqueness

private
  module ℝOrder =
    OrderedCommRingTheory ℝOrderedCommRing

evaluatePolynomialQuotient :
  (numerator denominator : List ℝ) →
  (∀ x → 0 ＃ evaluatePolynomial denominator x) →
  ℝ → ℝ
evaluatePolynomialQuotient
  numerator denominator denominator-apart =
    divideByApartDenominator
      (evaluatePolynomial numerator)
      (evaluatePolynomial denominator)
      denominator-apart

evaluatePolynomialQuotientDerivative :
  (numerator denominator : List ℝ) →
  (denominator-apart :
    ∀ x → 0 ＃ evaluatePolynomial denominator x) →
  ℝ → ℝ
evaluatePolynomialQuotientDerivative
  numerator denominator denominator-apart =
    divideByApartDenominatorDerivative
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
    divideByApartDenominatorHasDerivative
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
  derivative
    ≡
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

PolynomialQuotientDomain : List ℝ → Type
PolynomialQuotientDomain denominator =
  ApartDenominatorDomain
    (evaluatePolynomial denominator)

evaluatePolynomialQuotientOnDomain :
  (numerator denominator : List ℝ) →
  PolynomialQuotientDomain denominator → ℝ
evaluatePolynomialQuotientOnDomain numerator denominator =
  divideOnApartDenominatorDomain
    (evaluatePolynomial numerator)
    (evaluatePolynomial denominator)

evaluatePolynomialQuotientOnDomainDerivative :
  (numerator denominator : List ℝ) →
  PolynomialQuotientDomain denominator → ℝ
evaluatePolynomialQuotientOnDomainDerivative numerator denominator =
  divideOnApartDenominatorDomainConventionalDerivative
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
    divideOnApartDenominatorDomainHasConventionalDerivativeAlong
      (evaluatePolynomial numerator)
      (evaluatePolynomial denominator)
      (evaluatePolynomialDerivative numerator)
      (evaluatePolynomialDerivative denominator)
      (evaluatePolynomialHasDerivative numerator)
      (evaluatePolynomialHasDerivative denominator)

-- A first closed rational-function example.  The denominator is globally
-- apart from zero because a square is nonnegative, so callers do not have to
-- carry a domain hypothesis.
onePlusSquare : ℝ → ℝ
onePlusSquare x = 1 + x · x

onePlusSquareDerivative : ℝ → ℝ
onePlusSquareDerivative x = 0 + (1 · x + x · 1)

onePlusSquarePositive : ∀ x → 0 <ℝ onePlusSquare x
onePlusSquarePositive x =
  subst
    (_<ℝ onePlusSquare x)
    (addIdL 0)
    (<≤ℝ-add
      0 1 0 (x · x)
      (isOrderedCommRingℝ .IsOrderedCommRing.0<1)
      (ℝOrder.0≤² x))

onePlusSquareApart : ∀ x → 0 ＃ onePlusSquare x
onePlusSquareApart x =
  inl (onePlusSquarePositive x)

onePlusSquareHasDerivative :
  IsDerivative onePlusSquare onePlusSquareDerivative
onePlusSquareHasDerivative =
  addHasDerivative
    (const 1) (λ x → x · x)
    (const 0) onePlusSquareDerivativeTail
    (constantHasDerivative 1)
    (mulHasDerivative
      (idfun ℝ) (idfun ℝ)
      (const 1) (const 1)
      identityHasDerivative identityHasDerivative)
  where
  onePlusSquareDerivativeTail : ℝ → ℝ
  onePlusSquareDerivativeTail x = 1 · x + x · 1

identityOverOnePlusSquare : ℝ → ℝ
identityOverOnePlusSquare =
  divideByApartDenominator
    (idfun ℝ) onePlusSquare onePlusSquareApart

identityOverOnePlusSquareDerivative : ℝ → ℝ
identityOverOnePlusSquareDerivative =
  divideByApartDenominatorDerivative
    (idfun ℝ) onePlusSquare onePlusSquareApart
    (const 1) onePlusSquareDerivative

identityOverOnePlusSquareHasDerivative :
  IsDerivative
    identityOverOnePlusSquare
    identityOverOnePlusSquareDerivative
identityOverOnePlusSquareHasDerivative =
  divideByApartDenominatorHasDerivative
    (idfun ℝ) onePlusSquare onePlusSquareApart
    (const 1) onePlusSquareDerivative
    identityHasDerivative onePlusSquareHasDerivative

open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Operations
  public

open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Composition
  public

open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.CombinedDenominator
  public

open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.GeometricTail
  public

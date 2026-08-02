module Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.GeometricTail where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List using (List ; length)
open import Cubical.Data.Sum using (inl)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Basic
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Polynomial
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Power
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Domain
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.NormalForm
open import Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Affine
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.EventuallyGeometric

geometricTailDenominator : ℝ → ℝ → ℝ
geometricTailDenominator ratio x =
  1 - ratio · x

geometricTailDenominatorDerivative : ℝ → ℝ → ℝ
geometricTailDenominatorDerivative ratio x =
  0 - (0 · x + ratio · 1)

geometricTailDenominatorHasDerivative : ∀ ratio →
  IsDerivative
    (geometricTailDenominator ratio)
    (geometricTailDenominatorDerivative ratio)
geometricTailDenominatorHasDerivative ratio =
  subHasDerivative
    (const 1) (λ x → ratio · x)
    (const 0) (λ x → 0 · x + ratio · 1)
    (constantHasDerivative 1)
    (mulHasDerivative
      (const ratio) (idfun ℝ)
      (const 0) (const 1)
      (constantHasDerivative ratio)
      identityHasDerivative)

polynomialGeometricTailNumerator :
  List ℝ → ℝ → ℝ → ℝ
polynomialGeometricTailNumerator
  prefix coefficient x =
    coefficient · x ^ⁿ length prefix

polynomialGeometricTailNumeratorDerivative :
  List ℝ → ℝ → ℝ → ℝ
polynomialGeometricTailNumeratorDerivative
  prefix coefficient x =
    0 · x ^ⁿ length prefix
      + coefficient
        · naturalPowerDerivative
            (length prefix) x

polynomialGeometricTailNumeratorHasDerivative :
  ∀ prefix coefficient →
  IsDerivative
    (polynomialGeometricTailNumerator
      prefix coefficient)
    (polynomialGeometricTailNumeratorDerivative
      prefix coefficient)
polynomialGeometricTailNumeratorHasDerivative
  prefix coefficient =
    mulHasDerivative
      (const coefficient)
      (λ x → x ^ⁿ length prefix)
      (const 0)
      (naturalPowerDerivative (length prefix))
      (constantHasDerivative coefficient)
      (naturalPowerHasDerivative (length prefix))

polynomialGeometricRationalNumerator :
  List ℝ → ℝ → ℝ → ℝ → ℝ
polynomialGeometricRationalNumerator
  prefix coefficient ratio x =
    evaluatePolynomial prefix x
      · geometricTailDenominator ratio x
    + polynomialGeometricTailNumerator
        prefix coefficient x

polynomialGeometricRationalNumeratorDerivative :
  List ℝ → ℝ → ℝ → ℝ → ℝ
polynomialGeometricRationalNumeratorDerivative
  prefix coefficient ratio x =
    evaluatePolynomialDerivative prefix x
        · geometricTailDenominator ratio x
      + evaluatePolynomial prefix x
        · geometricTailDenominatorDerivative ratio x
    + polynomialGeometricTailNumeratorDerivative
        prefix coefficient x

polynomialGeometricRationalNumeratorHasDerivative :
  ∀ prefix coefficient ratio →
  IsDerivative
    (polynomialGeometricRationalNumerator
      prefix coefficient ratio)
    (polynomialGeometricRationalNumeratorDerivative
      prefix coefficient ratio)
polynomialGeometricRationalNumeratorHasDerivative
  prefix coefficient ratio =
    addHasDerivative
      (λ x →
        evaluatePolynomial prefix x
          · geometricTailDenominator ratio x)
      (polynomialGeometricTailNumerator
        prefix coefficient)
      (λ x →
        evaluatePolynomialDerivative prefix x
            · geometricTailDenominator ratio x
          + evaluatePolynomial prefix x
            · geometricTailDenominatorDerivative ratio x)
      (polynomialGeometricTailNumeratorDerivative
        prefix coefficient)
      (mulHasDerivative
        (evaluatePolynomial prefix)
        (geometricTailDenominator ratio)
        (evaluatePolynomialDerivative prefix)
        (geometricTailDenominatorDerivative ratio)
        (evaluatePolynomialHasDerivative prefix)
        (geometricTailDenominatorHasDerivative ratio))
      (polynomialGeometricTailNumeratorHasDerivative
        prefix coefficient)

PolynomialGeometricRationalDomain : ℝ → Type
PolynomialGeometricRationalDomain ratio =
  ApartDenominatorDomain
    (geometricTailDenominator ratio)

polynomialGeometricRationalFunction :
  List ℝ → ℝ → ∀ ratio →
  PolynomialGeometricRationalDomain ratio → ℝ
polynomialGeometricRationalFunction
  prefix coefficient ratio =
    divideOnApartDenominatorDomain
      (polynomialGeometricRationalNumerator
        prefix coefficient ratio)
      (geometricTailDenominator ratio)

polynomialGeometricRationalFunctionDerivative :
  List ℝ → ℝ → ∀ ratio →
  PolynomialGeometricRationalDomain ratio → ℝ
polynomialGeometricRationalFunctionDerivative
  prefix coefficient ratio =
    divideOnApartDenominatorDomainConventionalDerivative
      (polynomialGeometricRationalNumerator
        prefix coefficient ratio)
      (geometricTailDenominator ratio)
      (polynomialGeometricRationalNumeratorDerivative
        prefix coefficient ratio)
      (geometricTailDenominatorDerivative ratio)

polynomialGeometricRationalFunctionHasDerivativeAlong :
  ∀ prefix coefficient ratio →
  IsDerivativeAlong
    (snd
      (ApartDenominatorDomainPremetricSpace
        (geometricTailDenominator ratio)))
    apartDenominatorDomainCoordinate
    (polynomialGeometricRationalFunction
      prefix coefficient ratio)
    (polynomialGeometricRationalFunctionDerivative
      prefix coefficient ratio)
polynomialGeometricRationalFunctionHasDerivativeAlong
  prefix coefficient ratio =
    divideOnApartDenominatorDomainHasConventionalDerivativeAlong
      (polynomialGeometricRationalNumerator
        prefix coefficient ratio)
      (geometricTailDenominator ratio)
      (polynomialGeometricRationalNumeratorDerivative
        prefix coefficient ratio)
      (geometricTailDenominatorDerivative ratio)
      (polynomialGeometricRationalNumeratorHasDerivative
        prefix coefficient ratio)
      (geometricTailDenominatorHasDerivative ratio)

geometricTailDenominatorPositive : ∀ ratio x →
  RationalContractionBound (ratio · x) →
  0 <ℝ geometricTailDenominator ratio x
geometricTailDenominatorPositive
  ratio x contraction =
    positiveSub (ratio · x) 1
      (rationalContractionBound→x<1
        (ratio · x) contraction)

polynomialGeometricRationalDomainPoint : ∀ ratio x →
  RationalContractionBound (ratio · x) →
  PolynomialGeometricRationalDomain ratio
polynomialGeometricRationalDomainPoint
  ratio x contraction =
    x
    , inl
        (geometricTailDenominatorPositive
          ratio x contraction)

polynomialGeometricRationalFunction-expand :
  ∀ prefix coefficient ratio
    (point : PolynomialGeometricRationalDomain ratio) →
  polynomialGeometricRationalFunction
      prefix coefficient ratio point
    ≡
  evaluatePolynomial prefix (fst point)
    + polynomialGeometricTailNumerator
        prefix coefficient (fst point)
      · inverseℝ
          (geometricTailDenominator ratio (fst point))
          (snd point)
polynomialGeometricRationalFunction-expand
  prefix coefficient ratio point =
    mulDistL
      (evaluatePolynomial prefix x
        · geometricTailDenominator ratio x)
      (polynomialGeometricTailNumerator
        prefix coefficient x)
      inverse
    ∙ cong
        (_+ polynomialGeometricTailNumerator
              prefix coefficient x · inverse)
        ( mulAssoc
            (evaluatePolynomial prefix x)
            (geometricTailDenominator ratio x)
            inverse
        ∙ cong
            (evaluatePolynomial prefix x ·_)
            (inverseℝLaw
              (geometricTailDenominator ratio x)
              (snd point))
        ∙ mulIdR (evaluatePolynomial prefix x)
        )
  where
  x : ℝ
  x = fst point

  inverse : ℝ
  inverse =
    inverseℝ
      (geometricTailDenominator ratio x)
      (snd point)

polynomialGeometricRationalFunction-atContraction :
  ∀ prefix coefficient ratio x →
  (contraction : RationalContractionBound (ratio · x)) →
  polynomialGeometricRationalFunction
      prefix coefficient ratio
      (polynomialGeometricRationalDomainPoint
        ratio x contraction)
    ≡
  evaluatePolynomial prefix x
    + (coefficient · x ^ⁿ length prefix)
      · geometricReciprocal
          (ratio · x) contraction
polynomialGeometricRationalFunction-atContraction
  prefix coefficient ratio x contraction =
    polynomialGeometricRationalFunction-expand
      prefix coefficient ratio
      (polynomialGeometricRationalDomainPoint
        ratio x contraction)

powerSeriesValue-polynomialGeometric≡rationalFunction :
  ∀ prefix coefficient ratio x →
  (contraction : RationalContractionBound (ratio · x)) →
  (summable :
    PowerSeriesSummableAt
      (polynomialGeometricCoefficients
        prefix coefficient ratio)
      x) →
  powerSeriesValue
      (polynomialGeometricCoefficients
        prefix coefficient ratio)
      x summable
    ≡
  polynomialGeometricRationalFunction
    prefix coefficient ratio
    (polynomialGeometricRationalDomainPoint
      ratio x contraction)
powerSeriesValue-polynomialGeometric≡rationalFunction
  prefix coefficient ratio x
  contraction summable =
    powerSeriesValue-polynomialGeometric
      prefix coefficient ratio x
      contraction summable
    ∙ sym
        (polynomialGeometricRationalFunction-atContraction
          prefix coefficient ratio x contraction)

module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Polynomial.Derivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List
  using (List ; [] ; _∷_)
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)
import Cubical.Data.Nat as Nat

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.Polynomial
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Uniform
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Polynomial
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Polynomial.Uniform
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Uniform

open import Cubical.Relation.Premetric.Base

weightPolynomialCoefficientSequence :
  ∀ start coefficients n →
  polynomialCoefficientSequence
      (weightPolynomialCoefficients
        start coefficients)
      n
    ≡
  realNatural (start Nat.+ n)
    · polynomialCoefficientSequence
        coefficients n
weightPolynomialCoefficientSequence
  start [] n =
    sym
      (mulZeroR
        (realNatural (start Nat.+ n)))
weightPolynomialCoefficientSequence
  start (coefficient ∷ coefficients) zero =
    cong
      (_· coefficient)
      (cong realNatural
        (sym (Nat.+-zero start)))
weightPolynomialCoefficientSequence
  start (coefficient ∷ coefficients) (suc n) =
    weightPolynomialCoefficientSequence
      (suc start) coefficients n
    ∙ cong
        (_· polynomialCoefficientSequence
          coefficients n)
        (cong realNatural
          (sym (Nat.+-suc start n)))

formalDerivativePolynomialCoefficientSequence :
  ∀ coefficients →
  formalDerivative
      (polynomialCoefficientSequence coefficients)
    ≡
  polynomialCoefficientSequence
    (polynomialDerivativeCoefficients coefficients)
formalDerivativePolynomialCoefficientSequence [] =
  funExt
    (λ n →
      mulZeroR (realNatural (suc n)))
formalDerivativePolynomialCoefficientSequence
  (constant ∷ coefficients) =
    funExt
      (λ n →
        sym
          (weightPolynomialCoefficientSequence
            (suc zero) coefficients n))

polynomialFormalDerivativePowerSeriesValue :
  ∀ coefficients x →
  (summable :
    PowerSeriesSummableAt
      (formalDerivative
        (polynomialCoefficientSequence coefficients))
      x) →
  powerSeriesValue
      (formalDerivative
        (polynomialCoefficientSequence coefficients))
      x summable
    ≡
  evaluatePolynomialDerivative coefficients x
polynomialFormalDerivativePowerSeriesValue
  coefficients x summable =
    seriesSumPresPath
      formal-terms polynomial-terms
      terms-path
      summable
      (polynomialPowerSeriesSummable
        derivative-coefficients x)
    ∙ polynomialPowerSeriesValue
        derivative-coefficients x
        (polynomialPowerSeriesSummable
          derivative-coefficients x)
    ∙ evaluatePolynomialDerivativeCoefficients
        coefficients x
  where
  derivative-coefficients : List ℝ
  derivative-coefficients =
    polynomialDerivativeCoefficients coefficients

  formal-terms polynomial-terms : RealSequence
  formal-terms =
    powerSeriesTerms
      (formalDerivative
        (polynomialCoefficientSequence coefficients))
      x
  polynomial-terms =
    powerSeriesTerms
      (polynomialCoefficientSequence
        derivative-coefficients)
      x

  terms-path : formal-terms ≡ polynomial-terms
  terms-path =
    cong
      (λ coefficient-sequence →
        powerSeriesTerms coefficient-sequence x)
      (formalDerivativePolynomialCoefficientSequence
        coefficients)

polynomialFormalDerivativeUniformlyCauchyOnRadius :
  ∀ coefficients radius →
  PowerSeriesUniformlyCauchyOnRadius
    (formalDerivative
      (polynomialCoefficientSequence coefficients))
    radius
polynomialFormalDerivativeUniformlyCauchyOnRadius
  coefficients radius =
    subst
      (λ coefficient-sequence →
        PowerSeriesUniformlyCauchyOnRadius
          coefficient-sequence radius)
      (sym
        (formalDerivativePolynomialCoefficientSequence
          coefficients))
      (polynomialPowerSeriesUniformlyCauchyOnRadius
        (polynomialDerivativeCoefficients coefficients)
        radius)

polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius :
  List ℝ →
  ∀ radius →
  ClosedAbsRadius radius →
  ℝ
polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius
  coefficients radius =
    powerSeriesUniformValueOnClosedRadius
      (formalDerivative
        (polynomialCoefficientSequence coefficients))
      radius
      (polynomialFormalDerivativeUniformlyCauchyOnRadius
        coefficients radius)

polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius-value :
  ∀ coefficients radius point →
  polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius
      coefficients radius point
    ≡
  evaluatePolynomialDerivative
    coefficients (fst point)
polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius-value
  coefficients radius point =
    polynomialFormalDerivativePowerSeriesValue
      coefficients (fst point)
      (uniformlyCauchySeriesSummableAt
        (ClosedAbsRadius radius)
        (powerSeriesTermsOnClosedRadius
          (formalDerivative
            (polynomialCoefficientSequence coefficients))
          radius)
        (polynomialFormalDerivativeUniformlyCauchyOnRadius
          coefficients radius)
        point)

-- The finite power-series derivative now has the same canonical value as the
-- Horner derivative.  This is the commuting bridge between the algebraic
-- polynomial theorem and coefficientwise termwise differentiation.
polynomialPowerSeriesFunctionHasFormalDerivativeOnClosedRadius :
  ∀ coefficients radius →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (polynomialPowerSeriesFunctionOnClosedRadius
      coefficients radius)
    (polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius
      coefficients radius)
polynomialPowerSeriesFunctionHasFormalDerivativeOnClosedRadius
  coefficients radius =
    subst
      (λ derivative →
        IsDerivativeAlong
          (snd (ClosedAbsRadiusPremetricSpace radius))
          fst
          (polynomialPowerSeriesFunctionOnClosedRadius
            coefficients radius)
          derivative)
      (sym
        (funExt
          (polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius-value
            coefficients radius)))
      (polynomialPowerSeriesFunctionHasDerivativeOnClosedRadius
        coefficients radius)

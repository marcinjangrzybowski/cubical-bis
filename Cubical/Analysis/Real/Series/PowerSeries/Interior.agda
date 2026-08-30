module Cubical.Analysis.Real.Series.PowerSeries.Interior where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Interior


-- A closed-radius uniform sum has its ordinary ambient derivative at every
-- strict interior point, provided the ambient function explicitly agrees
-- with that sum on the closed radius.

powerSeriesUniformValueHasFormalDerivativeAtInteriorWithExtension :
  ∀ coefficients radius →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius coefficients radius) →
  (derivative-uniform :
    FormalDerivativePowerSeriesUniformlyCauchyOnRadius
      coefficients radius) →
  (factor-uniform :
    PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
      coefficients radius) →
  (function : ℝ → ℝ) →
  (∀ point →
    function (fst point)
      ≡
    powerSeriesUniformValueOnClosedRadius
      coefficients radius uniform point) →
  ∀ x →
  (interior : absℝ x <ℝ radius) →
  IsDerivativeAt
    function
    (formalDerivativePowerSeriesUniformValueOnClosedRadius
      coefficients radius derivative-uniform
      (x , <ℝ-weaken (absℝ x) radius interior))
    x
powerSeriesUniformValueHasFormalDerivativeAtInteriorWithExtension
  coefficients radius uniform derivative-uniform factor-uniform
  function agrees x interior =
  closedAbsRadiusDerivativeAtInteriorWithExtension
    radius
    (powerSeriesUniformValueOnClosedRadius
      coefficients radius uniform)
    (formalDerivativePowerSeriesUniformValueOnClosedRadius
      coefficients radius derivative-uniform)
    function
    (powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
      coefficients radius uniform derivative-uniform factor-uniform)
    agrees x interior


-- Moving a derivative-majorant Cauchy witness inward is kept separate from
-- the derivative theorem.  Besides reducing normalization, this witness is
-- useful for continuity and subsequent termwise operations.

formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorantWithin :
  ∀ coefficients majorant inner-radius outer-radius →
  CoefficientMajorizedBy coefficients majorant →
  0ℝ ≤ℝ inner-radius →
  inner-radius ≤ℝ outer-radius →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant majorant) outer-radius) →
  FormalDerivativePowerSeriesUniformlyCauchyOnRadius
    coefficients inner-radius
formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorantWithin
  coefficients majorant inner-radius outer-radius
  majorized inner-nonnegative inner≤outer
  outer-derivative-majorant-cauchy =
  formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
    coefficients majorant inner-radius majorized
    inner-derivative-majorant-cauchy
  where
  derivative-majorant-nonnegative :
    NonnegativeCoefficients
      (formalDerivativeMajorant majorant)
  derivative-majorant-nonnegative =
    formalDerivativeMajorant-nonnegative
      majorant
      (coefficientMajorantIsNonnegative
        coefficients majorant majorized)

  abs-inner≤outer : absℝ inner-radius ≤ℝ outer-radius
  abs-inner≤outer =
    subst
      (_≤ℝ outer-radius)
      (sym
        (absOfNonnegative
          inner-radius inner-nonnegative))
      inner≤outer

  inner-derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) inner-radius)
  inner-derivative-majorant-cauchy =
    dominatedCauchySeriesIsCauchy
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) inner-radius)
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) outer-radius)
      (powerSeriesTermAbsBoundByCoefficientMajorant
        (formalDerivativeMajorant majorant)
        (formalDerivativeMajorant majorant)
        inner-radius outer-radius
        (nonnegativeCoefficientsSelfMajorized
          (formalDerivativeMajorant majorant)
          derivative-majorant-nonnegative)
        abs-inner≤outer)
      outer-derivative-majorant-cauchy


powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinExtension :
  ∀ coefficients majorant inner-radius outer-radius →
  (majorized : CoefficientMajorizedBy coefficients majorant) →
  (inner-nonnegative : 0ℝ ≤ℝ inner-radius) →
  (inner≤outer : inner-radius ≤ℝ outer-radius) →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius
      coefficients inner-radius) →
  (outer-derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) outer-radius)) →
  (function : ℝ → ℝ) →
  (∀ point →
    function (fst point)
      ≡
    powerSeriesUniformValueOnClosedRadius
      coefficients inner-radius uniform point) →
  ∀ x →
  (interior : absℝ x <ℝ inner-radius) →
  Σ[ derivative-uniform ∈
      FormalDerivativePowerSeriesUniformlyCauchyOnRadius
        coefficients inner-radius ]
    IsDerivativeAt
      function
      (formalDerivativePowerSeriesUniformValueOnClosedRadius
        coefficients inner-radius derivative-uniform
        (x , <ℝ-weaken
          (absℝ x) inner-radius interior))
      x
powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinExtension
  coefficients majorant inner-radius outer-radius
  majorized inner-nonnegative inner≤outer uniform
  outer-derivative-majorant-cauchy function agrees x interior =
  derivative-uniform
  , powerSeriesUniformValueHasFormalDerivativeAtInteriorWithExtension
      coefficients inner-radius uniform
      derivative-uniform factor-uniform
      function agrees x interior
  where
  derivative-uniform :
    FormalDerivativePowerSeriesUniformlyCauchyOnRadius
      coefficients inner-radius
  derivative-uniform =
    formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorantWithin
      coefficients majorant inner-radius outer-radius
      majorized inner-nonnegative inner≤outer
      outer-derivative-majorant-cauchy

  factor-uniform :
    PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
      coefficients inner-radius
  factor-uniform =
    powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithin
      coefficients majorant inner-radius outer-radius
      majorized inner-nonnegative inner≤outer
      outer-derivative-majorant-cauchy


powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinStrictExtension :
  ∀ coefficients majorant inner-radius outer-radius →
  (majorized : CoefficientMajorizedBy coefficients majorant) →
  (inner-nonnegative : 0ℝ ≤ℝ inner-radius) →
  (inner<outer : inner-radius <ℝ outer-radius) →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius
      coefficients inner-radius) →
  (outer-derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) outer-radius)) →
  (function : ℝ → ℝ) →
  (∀ point →
    function (fst point)
      ≡
    powerSeriesUniformValueOnClosedRadius
      coefficients inner-radius uniform point) →
  ∀ x →
  (interior : absℝ x <ℝ inner-radius) →
  Σ[ derivative-uniform ∈
      FormalDerivativePowerSeriesUniformlyCauchyOnRadius
        coefficients inner-radius ]
    IsDerivativeAt
      function
      (formalDerivativePowerSeriesUniformValueOnClosedRadius
        coefficients inner-radius derivative-uniform
        (x , <ℝ-weaken
          (absℝ x) inner-radius interior))
      x
powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinStrictExtension
  coefficients majorant inner-radius outer-radius
  majorized inner-nonnegative inner<outer uniform
  outer-derivative-majorant-cauchy function agrees x interior =
  powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinExtension
    coefficients majorant inner-radius outer-radius
    majorized inner-nonnegative
    (<ℝ-weaken inner-radius outer-radius inner<outer)
    uniform outer-derivative-majorant-cauchy
    function agrees x interior

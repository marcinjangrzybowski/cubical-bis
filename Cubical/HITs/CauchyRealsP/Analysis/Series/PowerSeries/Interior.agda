module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Interior where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Interior
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Majorant
open import Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Uniform
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference.Uniform
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference.Derivative

-- The closed-radius divided-difference theorem yields an ordinary derivative
-- at every strict interior point as soon as the uniform sum agrees with a
-- supplied ambient function.  This avoids claiming that the canonical sum is
-- defined beyond the radius where summability is known.
powerSeriesUniformValueHasFormalDerivativeAtInteriorWithExtension :
  ∀ coefficients radius →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius
      coefficients radius) →
  (derivative-uniform :
    PowerSeriesUniformlyCauchyOnRadius
      (formalDerivative coefficients)
      radius) →
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
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients)
      radius derivative-uniform
      (x , <ℝ-weaken (absℝ x) radius interior))
    x
powerSeriesUniformValueHasFormalDerivativeAtInteriorWithExtension
  coefficients radius uniform
  derivative-uniform factor-uniform
  function agrees x interior =
    closedAbsRadiusDerivativeAtInteriorWithExtension
      radius
      (powerSeriesUniformValueOnClosedRadius
        coefficients radius uniform)
      (powerSeriesUniformValueOnClosedRadius
        (formalDerivative coefficients)
        radius derivative-uniform)
      function
      (powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
        coefficients radius uniform
        derivative-uniform factor-uniform)
      agrees x interior

-- Convergence of a nonnegative derivative majorant at an outer radius is
-- enough for the ordinary derivative at strict interior points of a smaller
-- radius.  The ambient function is still explicit, as is its agreement with
-- the canonical uniform sum on the inner closed radius.
powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinExtension :
  ∀ coefficients majorant inner-radius outer-radius →
  (majorized :
    CoefficientMajorizedBy coefficients majorant) →
  (nonnegative :
    NonnegativeCoefficients majorant) →
  (inner-nonnegative : 0 ≤ℝ inner-radius) →
  (inner≤outer : inner-radius ≤ℝ outer-radius) →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius
      coefficients inner-radius) →
  (outer-derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant)
        outer-radius)) →
  (function : ℝ → ℝ) →
  (∀ point →
    function (fst point)
      ≡
    powerSeriesUniformValueOnClosedRadius
      coefficients inner-radius uniform point) →
  ∀ x →
  (interior : absℝ x <ℝ inner-radius) →
  IsDerivativeAt
    function
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients)
      inner-radius
      (formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorantWithin
        coefficients majorant
        inner-radius outer-radius
        majorized nonnegative
        inner-nonnegative inner≤outer
        outer-derivative-majorant-cauchy)
      (x , <ℝ-weaken
        (absℝ x) inner-radius interior))
    x
powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinExtension
  coefficients majorant inner-radius outer-radius
  majorized nonnegative inner-nonnegative
  inner≤outer uniform
  outer-derivative-majorant-cauchy
  function agrees x interior =
    closedAbsRadiusDerivativeAtInteriorWithExtension
      inner-radius
      (powerSeriesUniformValueOnClosedRadius
        coefficients inner-radius uniform)
      (powerSeriesUniformValueOnClosedRadius
        (formalDerivative coefficients)
        inner-radius derivative-uniform)
      function
      (powerSeriesUniformValueHasFormalDerivativeByMajorantWithin
        coefficients majorant
        inner-radius outer-radius
        majorized nonnegative inner-nonnegative
        inner≤outer uniform
        outer-derivative-majorant-cauchy)
      agrees x interior
  where
  derivative-uniform :
    PowerSeriesUniformlyCauchyOnRadius
      (formalDerivative coefficients)
      inner-radius
  derivative-uniform =
    formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorantWithin
      coefficients majorant
      inner-radius outer-radius
      majorized nonnegative
      inner-nonnegative inner≤outer
      outer-derivative-majorant-cauchy

powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinStrictExtension :
  ∀ coefficients majorant inner-radius outer-radius →
  (majorized :
    CoefficientMajorizedBy coefficients majorant) →
  (nonnegative :
    NonnegativeCoefficients majorant) →
  (inner-nonnegative : 0 ≤ℝ inner-radius) →
  (inner<outer : inner-radius <ℝ outer-radius) →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius
      coefficients inner-radius) →
  (outer-derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant)
        outer-radius)) →
  (function : ℝ → ℝ) →
  (∀ point →
    function (fst point)
      ≡
    powerSeriesUniformValueOnClosedRadius
      coefficients inner-radius uniform point) →
  ∀ x →
  (interior : absℝ x <ℝ inner-radius) →
  IsDerivativeAt
    function
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients)
      inner-radius
      (formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorantWithin
        coefficients majorant
        inner-radius outer-radius
        majorized nonnegative inner-nonnegative
        (<ℝ-weaken
          inner-radius outer-radius inner<outer)
        outer-derivative-majorant-cauchy)
      (x , <ℝ-weaken
        (absℝ x) inner-radius interior))
    x
powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinStrictExtension
  coefficients majorant inner-radius outer-radius
  majorized nonnegative inner-nonnegative
  inner<outer uniform
  outer-derivative-majorant-cauchy
  function agrees x interior =
    powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinExtension
      coefficients majorant
      inner-radius outer-radius
      majorized nonnegative inner-nonnegative
      (<ℝ-weaken
        inner-radius outer-radius inner<outer)
      uniform outer-derivative-majorant-cauchy
      function agrees x interior

module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference.Derivative where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Uniform
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Majorant
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Uniform
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference.Sum
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference.Uniform

-- The canonical uniform sum of a power series has the canonical uniform sum
-- of its formal derivative as derivative on the closed-radius subspace,
-- provided the two series and their divided-difference family converge
-- uniformly there.
powerSeriesUniformValueHasFormalDerivativeOnClosedRadius :
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
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (powerSeriesUniformValueOnClosedRadius
      coefficients radius uniform)
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients)
      radius derivative-uniform)
powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
  coefficients radius
  uniform derivative-uniform factor-uniform =
    continuousDifferenceFactorGivesDerivative
      (snd (ClosedAbsRadiusPremetricSpace radius))
      fst
      (powerSeriesUniformValueOnClosedRadius
        coefficients radius uniform)
      (powerSeriesUniformValueOnClosedRadius
        (formalDerivative coefficients)
        radius derivative-uniform)
      (powerSeriesDifferenceFactorValueOnClosedRadius
        coefficients radius factor-uniform)
      factorization
      diagonal
      (powerSeriesDifferenceFactorValueOnClosedRadiusIsContinuous
        coefficients radius factor-uniform)
  where
  original-summable :
    ∀ point →
    PowerSeriesSummableAt
      coefficients (fst point)
  original-summable point =
    uniformlyCauchySeriesSummableAt
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius
        coefficients radius)
      uniform point

  derivative-summable :
    ∀ point →
    PowerSeriesSummableAt
      (formalDerivative coefficients)
      (fst point)
  derivative-summable point =
    uniformlyCauchySeriesSummableAt
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius
        (formalDerivative coefficients)
        radius)
      derivative-uniform point

  factor-summable :
    ∀ point →
    Summable
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius point)
  factor-summable point =
    uniformlyCauchySeriesSummableAt
      (ClosedAbsRadiusPair radius)
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius)
      factor-uniform point

  factorization :
    ∀ x y →
    powerSeriesUniformValueOnClosedRadius
        coefficients radius uniform y
      -
    powerSeriesUniformValueOnClosedRadius
        coefficients radius uniform x
      ≡
    (fst y - fst x)
      · powerSeriesDifferenceFactorValueOnClosedRadius
          coefficients radius factor-uniform
          (x , y)
  factorization x y =
    powerSeriesValueDifferenceFactorization
      coefficients (fst x) (fst y)
      (original-summable x)
      (original-summable y)
      (factor-summable (x , y))

  diagonal :
    ∀ x →
    powerSeriesDifferenceFactorValueOnClosedRadius
        coefficients radius factor-uniform
        (x , x)
      ≡
    powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients)
      radius derivative-uniform x
  diagonal x =
    powerSeriesDifferenceFactorDiagonalValue
      coefficients (fst x)
      (factor-summable (x , x))
      (derivative-summable x)

-- A coefficient majorant with a convergent formal-derivative series supplies
-- both uniform hypotheses needed by the divided-difference theorem.  The
-- original series remains explicit because derivative convergence alone does
-- not determine its constant term.
powerSeriesUniformValueHasFormalDerivativeByMajorant :
  ∀ coefficients majorant radius →
  (majorized :
    CoefficientMajorizedBy coefficients majorant) →
  (nonnegative :
    NonnegativeCoefficients majorant) →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius
      coefficients radius) →
  (derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant)
        radius)) →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (powerSeriesUniformValueOnClosedRadius
      coefficients radius uniform)
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients)
      radius
      (formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
        coefficients majorant radius
        majorized nonnegative
        derivative-majorant-cauchy))
powerSeriesUniformValueHasFormalDerivativeByMajorant
  coefficients majorant radius
  majorized nonnegative uniform
  derivative-majorant-cauchy =
    powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
      coefficients radius uniform
      (formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
        coefficients majorant radius
        majorized nonnegative
        derivative-majorant-cauchy)
      (powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
        coefficients majorant radius
        majorized nonnegative
        derivative-majorant-cauchy)

-- The closed-boundary theorem above asks for derivative-majorant convergence
-- at the same radius.  For an inner closed radius it is enough to know that
-- convergence at any larger nonnegative radius.
powerSeriesUniformValueHasFormalDerivativeByMajorantWithin :
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
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace inner-radius))
    fst
    (powerSeriesUniformValueOnClosedRadius
      coefficients inner-radius uniform)
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients)
      inner-radius
      (formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorantWithin
        coefficients majorant
        inner-radius outer-radius
        majorized nonnegative
        inner-nonnegative inner≤outer
        outer-derivative-majorant-cauchy))
powerSeriesUniformValueHasFormalDerivativeByMajorantWithin
  coefficients majorant inner-radius outer-radius
  majorized nonnegative inner-nonnegative
  inner≤outer uniform
  outer-derivative-majorant-cauchy =
    powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
      coefficients inner-radius uniform
      (formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorantWithin
        coefficients majorant
        inner-radius outer-radius
        majorized nonnegative
        inner-nonnegative inner≤outer
        outer-derivative-majorant-cauchy)
      (powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithin
        coefficients majorant
        inner-radius outer-radius
        majorized nonnegative
        inner-nonnegative inner≤outer
        outer-derivative-majorant-cauchy)

powerSeriesUniformValueHasFormalDerivativeByMajorantWithinStrict :
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
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace inner-radius))
    fst
    (powerSeriesUniformValueOnClosedRadius
      coefficients inner-radius uniform)
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients)
      inner-radius
      (formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorantWithin
        coefficients majorant
        inner-radius outer-radius
        majorized nonnegative inner-nonnegative
        (<ℝ-weaken
          inner-radius outer-radius inner<outer)
        outer-derivative-majorant-cauchy))
powerSeriesUniformValueHasFormalDerivativeByMajorantWithinStrict
  coefficients majorant inner-radius outer-radius
  majorized nonnegative inner-nonnegative
  inner<outer uniform
  outer-derivative-majorant-cauchy =
    powerSeriesUniformValueHasFormalDerivativeByMajorantWithin
      coefficients majorant inner-radius outer-radius
      majorized nonnegative inner-nonnegative
      (<ℝ-weaken
        inner-radius outer-radius inner<outer)
      uniform outer-derivative-majorant-cauchy

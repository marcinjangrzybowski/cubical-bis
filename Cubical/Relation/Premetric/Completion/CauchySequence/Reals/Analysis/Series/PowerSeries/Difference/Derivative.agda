module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Derivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
  using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Convergence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LinearGrowth
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Sum
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Uniform


-- Uniform convergence of the original series, its formal derivative, and
-- the divided-difference family is exactly the data needed for termwise
-- differentiation.  The conclusion is division-free and valid up to the
-- boundary of the closed-radius subspace.

powerSeriesUniformValueHasFormalDerivativeOnClosedRadius :
  ∀ coefficients radius →
  (uniform : PowerSeriesUniformlyCauchyOnRadius coefficients radius) →
  (derivative-uniform :
    PowerSeriesUniformlyCauchyOnRadius
      (formalDerivative coefficients) radius) →
  (factor-uniform :
    PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
      coefficients radius) →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (powerSeriesUniformValueOnClosedRadius
      coefficients radius uniform)
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients) radius derivative-uniform)
powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
  coefficients radius uniform derivative-uniform factor-uniform =
  continuousDifferenceFactorGivesDerivative
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (powerSeriesUniformValueOnClosedRadius coefficients radius uniform)
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients) radius derivative-uniform)
    (powerSeriesDifferenceFactorValueOnClosedRadius
      coefficients radius factor-uniform)
    factorization diagonal
    (powerSeriesDifferenceFactorValueOnClosedRadiusIsContinuous
      coefficients radius factor-uniform)
  where
  original-summable : ∀ point →
    PowerSeriesSummableAt coefficients (fst point)
  original-summable point =
    uniformlyCauchySeriesSummableAt
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius coefficients radius)
      uniform point

  derivative-summable : ∀ point →
    PowerSeriesSummableAt
      (formalDerivative coefficients) (fst point)
  derivative-summable point =
    uniformlyCauchySeriesSummableAt
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius
        (formalDerivative coefficients) radius)
      derivative-uniform point

  factor-summable : ∀ point →
    Summable
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius point)
  factor-summable point =
    uniformlyCauchySeriesSummableAt
      (ClosedAbsRadiusPair radius)
      (powerSeriesDifferenceFactorOnClosedRadius coefficients radius)
      factor-uniform point

  factorization : ∀ x y →
    powerSeriesUniformValueOnClosedRadius
        coefficients radius uniform y
      Group.-
    powerSeriesUniformValueOnClosedRadius
        coefficients radius uniform x
      ≡
    (fst y Group.- fst x) Mul.·
      powerSeriesDifferenceFactorValueOnClosedRadius
        coefficients radius factor-uniform (x , y)
  factorization x y =
    powerSeriesValueDifferenceFactorization
      coefficients (fst x) (fst y)
      (original-summable x) (original-summable y)
      (factor-summable (x , y))

  diagonal : ∀ x →
    powerSeriesDifferenceFactorValueOnClosedRadius
        coefficients radius factor-uniform (x , x)
      ≡
    powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients) radius derivative-uniform x
  diagonal x =
    powerSeriesDifferenceFactorDiagonalValue
      coefficients (fst x)
      (factor-summable (x , x))
      (derivative-summable x)


-- Majorization supplies both analytic auxiliary families.  Nonnegativity is
-- derived from `CoefficientMajorizedBy`, unlike the older representation's
-- theorem which requested the same fact a second time.

powerSeriesUniformValueHasFormalDerivativeByMajorant :
  ∀ coefficients majorant radius →
  (majorized : CoefficientMajorizedBy coefficients majorant) →
  (uniform : PowerSeriesUniformlyCauchyOnRadius coefficients radius) →
  (derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms (formalDerivativeMajorant majorant) radius)) →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (powerSeriesUniformValueOnClosedRadius coefficients radius uniform)
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients) radius
      (formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
        coefficients majorant radius
        majorized derivative-majorant-cauchy))
powerSeriesUniformValueHasFormalDerivativeByMajorant
  coefficients majorant radius majorized uniform
  derivative-majorant-cauchy =
  powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
    coefficients radius uniform
    (formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
      coefficients majorant radius
      majorized derivative-majorant-cauchy)
    (powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
      coefficients majorant radius
      majorized derivative-majorant-cauchy)


powerSeriesUniformValueHasFormalDerivativeByMajorantWithin :
  ∀ coefficients majorant inner-radius outer-radius →
  (majorized : CoefficientMajorizedBy coefficients majorant) →
  (inner-nonnegative : Real.ιℚ 0 ≤ℝ inner-radius) →
  (inner≤outer : inner-radius ≤ℝ outer-radius) →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius coefficients inner-radius) →
  (outer-derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) outer-radius)) →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace inner-radius))
    fst
    (powerSeriesUniformValueOnClosedRadius
      coefficients inner-radius uniform)
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients) inner-radius
      (formalDerivativePowerSeriesUniformlyCauchyWithin
        coefficients majorant inner-radius outer-radius
        majorized
        inner-nonnegative inner≤outer
        outer-derivative-majorant-cauchy))
powerSeriesUniformValueHasFormalDerivativeByMajorantWithin
  coefficients majorant inner-radius outer-radius
  majorized inner-nonnegative inner≤outer uniform outer-cauchy =
  powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
    coefficients inner-radius uniform
    (formalDerivativePowerSeriesUniformlyCauchyWithin
      coefficients majorant inner-radius outer-radius
      majorized inner-nonnegative inner≤outer outer-cauchy)
    (powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithin
      coefficients majorant inner-radius outer-radius
      majorized inner-nonnegative inner≤outer outer-cauchy)


-- For bounded coefficients, Mertens already proved convergence of the
-- linear-growth derivative majorant.  Hence every positive rational closed
-- radius below one gets a fully constructive termwise differentiation
-- theorem with no extra convergence or modulus arguments.

boundedPowerSeriesUniformValueHasFormalDerivative :
  ∀ C q coefficients →
  (coefficients-bounded : CoefficientAbsBound C coefficients) →
  (q<1 : fst q ℚ.< 1) →
  IsDerivativeAlong
    (snd
      (ClosedAbsRadiusPremetricSpace
        (Real.ιℚ (fst q))))
    fst
    (powerSeriesUniformValueOnClosedRadius
      coefficients (Real.ιℚ (fst q))
      (boundedPowerSeriesUniformlyCauchy
        C q coefficients coefficients-bounded q<1))
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients) (Real.ιℚ (fst q))
      (boundedPowerSeriesFormalDerivativeUniformlyCauchy
        C q coefficients coefficients-bounded q<1))
boundedPowerSeriesUniformValueHasFormalDerivative
  C q coefficients coefficients-bounded q<1 =
  powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
    coefficients (Real.ιℚ (fst q))
    (boundedPowerSeriesUniformlyCauchy
      C q coefficients coefficients-bounded q<1)
    (boundedPowerSeriesFormalDerivativeUniformlyCauchy
      C q coefficients coefficients-bounded q<1)
    (powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
      coefficients (constantCoefficientMajorant C)
      (Real.ιℚ (fst q))
      (coefficientAbsBoundIsMajorized
        C coefficients coefficients-bounded)
      (formalDerivativeConstantMajorantIsCauchyAtPositiveRational
        C q q<1))

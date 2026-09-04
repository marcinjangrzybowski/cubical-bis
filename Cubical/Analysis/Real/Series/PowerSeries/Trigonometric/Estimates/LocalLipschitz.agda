module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.LocalLipschitz where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Comparison
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Difference
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Sum
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import
  Cubical.Analysis.Real.Series.PowerSeries.Exponential.Convergence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean
open import
  Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Convergence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.SharpBounds


private
  entirePowerSeriesDifferenceBoundByExponential :
    ∀ coefficients
      (entire-uniform :
        EntirePowerSeriesUniformlyCauchy coefficients)
      (factor-uniform :
        EntirePowerSeriesDifferenceFactorUniformlyCauchy coefficients) →
    CoefficientMajorizedBy coefficients exponentialCoefficients →
    ∀ x y radius →
    0ℝ ≤ℝ radius →
    absℝ x ≤ℝ radius →
    absℝ y ≤ℝ radius →
    absℝ
      (entirePowerSeriesValue coefficients entire-uniform y
        - entirePowerSeriesValue coefficients entire-uniform x)
      ≤ℝ
    absℝ (y - x) · exponentialEntireValue radius
  entirePowerSeriesDifferenceBoundByExponential
      coefficients entire-uniform factor-uniform majorized
      x y radius 0≤radius absx≤radius absy≤radius =
    subst
      (_≤ℝ absℝ (y - x) · exponentialEntireValue radius)
      (sym absolute-factorization)
      (mulPres≤L
        (absℝ factor-value)
        (exponentialEntireValue radius)
        (absℝ (y - x))
        (0≤→isNonnegative
          (absℝ (y - x)) (absNonnegative (y - x)))
        factor-bound)
    where
    point : ClosedAbsRadiusPair radius
    point =
      (x , absx≤radius) , (y , absy≤radius)

    factor-terms : RealSequence
    factor-terms =
      powerSeriesDifferenceFactor coefficients x y

    factor-summable : Summable factor-terms
    factor-summable =
      uniformlyCauchySeriesSummableAt
        (factor-uniform radius) point

    factor-value : ℝ
    factor-value =
      seriesSum factor-terms factor-summable

    exponential-summable :
      PowerSeriesSummableAt exponentialCoefficients radius
    exponential-summable =
      entirePowerSeriesSummableAt
        exponentialCoefficients
        exponentialPowerSeriesEntireUniformlyCauchy radius

    factorization :
      entirePowerSeriesValue coefficients entire-uniform y
          - entirePowerSeriesValue coefficients entire-uniform x
        ≡
      (y - x) · factor-value
    factorization =
      powerSeriesValueDifferenceFactorization
        coefficients x y
        (entirePowerSeriesSummableAt
          coefficients entire-uniform x)
        (entirePowerSeriesSummableAt
          coefficients entire-uniform y)
        factor-summable

    absolute-factorization :
      absℝ
        (entirePowerSeriesValue coefficients entire-uniform y
          - entirePowerSeriesValue coefficients entire-uniform x)
        ≡
      absℝ (y - x) · absℝ factor-value
    absolute-factorization =
      cong absℝ factorization
      ∙ absMul (y - x) factor-value

    factor-term-bound : ∀ n →
      absℝ (factor-terms n) ≤ℝ
      powerSeriesTerms exponentialCoefficients radius n
    factor-term-bound n =
      subst
        (absℝ (factor-terms n) ≤ℝ_)
        (cong
          (λ bound → powerSeriesTerms bound radius n)
          formalDerivative-exponentialCoefficients)
        (powerSeriesDifferenceFactorTermBoundByDerivativeMajorant
          coefficients exponentialCoefficients x y radius
          majorized 0≤radius absx≤radius absy≤radius n)

    factor-bound :
      absℝ factor-value ≤ℝ exponentialEntireValue radius
    factor-bound =
      seriesSumAbsBoundBy
        factor-terms
        (powerSeriesTerms exponentialCoefficients radius)
        factor-summable exponential-summable factor-term-bound


-- On every closed absolute-value radius, both trigonometric functions are
-- Lipschitz with the explicit power-series majorant exp(radius).

sinℝ-absoluteDifferenceBoundOnRadius : ∀ x y radius →
  0ℝ ≤ℝ radius →
  absℝ x ≤ℝ radius →
  absℝ y ≤ℝ radius →
  absℝ (sinℝ y - sinℝ x)
    ≤ℝ
  absℝ (y - x) · exponentialEntireValue radius
sinℝ-absoluteDifferenceBoundOnRadius =
  entirePowerSeriesDifferenceBoundByExponential
    sineCoefficients
    sinePowerSeriesEntireUniformlyCauchy
    sinePowerSeriesDifferenceFactorEntireUniformlyCauchy
    sineCoefficientsMajorizedByExponential


cosℝ-absoluteDifferenceBoundOnRadius : ∀ x y radius →
  0ℝ ≤ℝ radius →
  absℝ x ≤ℝ radius →
  absℝ y ≤ℝ radius →
  absℝ (cosℝ y - cosℝ x)
    ≤ℝ
  absℝ (y - x) · exponentialEntireValue radius
cosℝ-absoluteDifferenceBoundOnRadius =
  entirePowerSeriesDifferenceBoundByExponential
    cosineCoefficients
    cosinePowerSeriesEntireUniformlyCauchy
    cosinePowerSeriesDifferenceFactorEntireUniformlyCauchy
    cosineCoefficientsMajorizedByExponential


-- Canonical bounds require no separately supplied radius.

absLeft≤absSum : ∀ x y →
  absℝ x ≤ℝ absℝ x + absℝ y
absLeft≤absSum x y =
  subst
    (_≤ℝ absℝ x + absℝ y)
    (addIdR (absℝ x))
    (addPres≤L 0ℝ (absℝ y) (absℝ x)
      (absNonnegative y))


absRight≤absSum : ∀ x y →
  absℝ y ≤ℝ absℝ x + absℝ y
absRight≤absSum x y =
  subst
    (_≤ℝ absℝ x + absℝ y)
    (addIdL (absℝ y))
    (addPres≤R 0ℝ (absℝ x) (absℝ y)
      (absNonnegative x))


absSumNonnegative : ∀ x y →
  0ℝ ≤ℝ absℝ x + absℝ y
absSumNonnegative x y =
  subst
    (_≤ℝ absℝ x + absℝ y)
    (addIdL 0ℝ)
    (addPres≤
      0ℝ (absℝ x) 0ℝ (absℝ y)
      (absNonnegative x) (absNonnegative y))


sinℝ-absoluteDifferenceBound : ∀ x y →
  absℝ (sinℝ y - sinℝ x)
    ≤ℝ
  absℝ (y - x) ·
    exponentialEntireValue (absℝ x + absℝ y)
sinℝ-absoluteDifferenceBound x y =
  sinℝ-absoluteDifferenceBoundOnRadius
    x y (absℝ x + absℝ y)
    (absSumNonnegative x y)
    (absLeft≤absSum x y)
    (absRight≤absSum x y)


cosℝ-absoluteDifferenceBound : ∀ x y →
  absℝ (cosℝ y - cosℝ x)
    ≤ℝ
  absℝ (y - x) ·
    exponentialEntireValue (absℝ x + absℝ y)
cosℝ-absoluteDifferenceBound x y =
  cosℝ-absoluteDifferenceBoundOnRadius
    x y (absℝ x + absℝ y)
    (absSumNonnegative x y)
    (absLeft≤absSum x y)
    (absRight≤absSum x y)


-- At the origin these specialize to the familiar first-order estimates,
-- with the exponential majorant recording the current series-only loss.

sinℝ-absBoundByLinearExponential : ∀ x →
  absℝ (sinℝ x)
    ≤ℝ
  absℝ x · exponentialEntireValue (absℝ x)
sinℝ-absBoundByLinearExponential x =
  subst2 _≤ℝ_
    (cong absℝ
      (cong (sinℝ x -_) sinℝ-zero ∙ subZero (sinℝ x)))
    (cong
      (_· exponentialEntireValue (absℝ x))
      (cong absℝ (subZero x)))
    (sinℝ-absoluteDifferenceBoundOnRadius
      0ℝ x (absℝ x)
      (absNonnegative x)
      (subst
        (_≤ℝ absℝ x)
        (sym absZero)
        (absNonnegative x))
      (≤ℝ-refl (absℝ x)))


cosℝ-one-absoluteDifferenceBound : ∀ x →
  absℝ (cosℝ x - 1ℝ)
    ≤ℝ
  absℝ x · exponentialEntireValue (absℝ x)
cosℝ-one-absoluteDifferenceBound x =
  subst2 _≤ℝ_
    (cong absℝ (cong (cosℝ x -_) cosℝ-zero))
    (cong
      (_· exponentialEntireValue (absℝ x))
      (cong absℝ (subZero x)))
    (cosℝ-absoluteDifferenceBoundOnRadius
      0ℝ x (absℝ x)
      (absNonnegative x)
      (subst
        (_≤ℝ absℝ x)
        (sym absZero)
        (absNonnegative x))
      (≤ℝ-refl (absℝ x)))


-- Independently of displacement, sharp pointwise bounds give diameter two.

sinℝ-absoluteDifference≤two : ∀ x y →
  absℝ (sinℝ x - sinℝ y) ≤ℝ 1ℝ + 1ℝ
sinℝ-absoluteDifference≤two x y =
  ≤ℝ-trans
    (absℝ (sinℝ x - sinℝ y))
    (absℝ (sinℝ x) + absℝ (sinℝ y))
    (1ℝ + 1ℝ)
    (absSubTriangle (sinℝ x) (sinℝ y))
    (addPres≤
      (absℝ (sinℝ x)) 1ℝ
      (absℝ (sinℝ y)) 1ℝ
      (sinℝ-abs≤one x) (sinℝ-abs≤one y))


cosℝ-absoluteDifference≤two : ∀ x y →
  absℝ (cosℝ x - cosℝ y) ≤ℝ 1ℝ + 1ℝ
cosℝ-absoluteDifference≤two x y =
  ≤ℝ-trans
    (absℝ (cosℝ x - cosℝ y))
    (absℝ (cosℝ x) + absℝ (cosℝ y))
    (1ℝ + 1ℝ)
    (absSubTriangle (cosℝ x) (cosℝ y))
    (addPres≤
      (absℝ (cosℝ x)) 1ℝ
      (absℝ (cosℝ y)) 1ℝ
      (cosℝ-abs≤one x) (cosℝ-abs≤one y))

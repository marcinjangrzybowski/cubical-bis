module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Continuity.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Comparison
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Difference
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Sum
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Calculus
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire


-- The divided-difference majorant is again exponential, since its formal
-- derivative has the same coefficients.  This bound is independent of the
-- later order and inverse theory of the exponential.
opaque
  exponentialEntireValue-absoluteDifferenceBoundOnRadius : ∀ x y radius →
    0ℝ ≤ℝ radius → absℝ x ≤ℝ radius → absℝ y ≤ℝ radius →
    absℝ (exponentialEntireValue y - exponentialEntireValue x) ≤ℝ
    absℝ (y - x) · exponentialEntireValue radius
  exponentialEntireValue-absoluteDifferenceBoundOnRadius
      x y radius nonnegative absx≤radius absy≤radius =
    subst (_≤ℝ absℝ (y - x) · exponentialEntireValue radius)
      (sym absolute-factorization)
      (mulPres≤L
        (absℝ factor-value) (exponentialEntireValue radius)
        (absℝ (y - x))
        (0≤→isNonnegative (absℝ (y - x)) (absNonnegative (y - x))) factor-bound)
    where
    factor-terms : RealSequence
    factor-terms = powerSeriesDifferenceFactor exponentialCoefficients x y

    factor-summable : Summable factor-terms
    factor-summable =
      uniformlyCauchySeriesSummableAt
        (exponentialPowerSeriesDifferenceFactorEntireUniformlyCauchy radius)
        ((x , absx≤radius) , (y , absy≤radius))

    factor-value : ℝ
    factor-value = seriesSum factor-terms factor-summable

    factorization :
      exponentialEntireValue y - exponentialEntireValue x ≡
      (y - x) · factor-value
    factorization =
      powerSeriesValueDifferenceFactorization exponentialCoefficients x y
        (entirePowerSeriesSummableAt
          exponentialCoefficients exponentialPowerSeriesEntireUniformlyCauchy x)
        (entirePowerSeriesSummableAt
          exponentialCoefficients exponentialPowerSeriesEntireUniformlyCauchy y)
        factor-summable

    absolute-factorization :
      absℝ (exponentialEntireValue y - exponentialEntireValue x) ≡
      absℝ (y - x) · absℝ factor-value
    absolute-factorization =
      cong absℝ factorization ∙ absMul (y - x) factor-value

    factor-term-bound : ∀ n →
      absℝ (factor-terms n) ≤ℝ
      powerSeriesTerms exponentialCoefficients radius n
    factor-term-bound n =
      subst (absℝ (factor-terms n) ≤ℝ_)
        (cong (λ coefficients → powerSeriesTerms coefficients radius n)
          formalDerivative-exponentialCoefficients)
        (powerSeriesDifferenceFactorTermBoundByDerivativeMajorant
          exponentialCoefficients exponentialCoefficients x y radius
          exponentialCoefficients-selfMajorized
          nonnegative absx≤radius absy≤radius n)

    factor-bound : absℝ factor-value ≤ℝ exponentialEntireValue radius
    factor-bound =
      seriesSumAbsBoundBy factor-terms
        (powerSeriesTerms exponentialCoefficients radius)
        factor-summable
        (entirePowerSeriesSummableAt
          exponentialCoefficients exponentialPowerSeriesEntireUniformlyCauchy radius)
        factor-term-bound

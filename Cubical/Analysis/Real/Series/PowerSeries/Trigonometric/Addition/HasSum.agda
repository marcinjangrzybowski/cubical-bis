module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.HasSum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.Product.Native
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


private
  trigonometricPowerSeriesIsAbsolutelyCauchy :
    ∀ coefficients →
    CoefficientMajorizedBy coefficients exponentialCoefficients →
    ∀ x → IsAbsolutelyCauchySeries (powerSeriesTerms coefficients x)
  trigonometricPowerSeriesIsAbsolutelyCauchy
      coefficients majorized x =
    dominatedCauchySeriesIsCauchy
      (absℝ ∘ powerSeriesTerms coefficients x)
      (powerSeriesTerms exponentialCoefficients (absℝ x))
      dominates
      (absoluteCauchySeriesIsCauchy
        (powerSeriesTerms exponentialCoefficients (absℝ x))
        (exponentialPowerSeriesIsAbsolutelyCauchyEverywhere (absℝ x)))
    where
    dominates : ∀ n →
      absℝ (absℝ (powerSeriesTerms coefficients x n)) ≤ℝ
      powerSeriesTerms exponentialCoefficients (absℝ x) n
    dominates n =
      subst
        (_≤ℝ powerSeriesTerms exponentialCoefficients (absℝ x) n)
        (sym (absIdem (powerSeriesTerms coefficients x n)))
        (powerSeriesTermAbsBoundByCoefficientMajorant
          coefficients exponentialCoefficients x (absℝ x)
          majorized (≤ℝ-refl (absℝ x)) n)


sinePowerSeriesIsAbsolutelyCauchy : ∀ x →
  IsAbsolutelyCauchySeries (powerSeriesTerms sineCoefficients x)
sinePowerSeriesIsAbsolutelyCauchy =
  trigonometricPowerSeriesIsAbsolutelyCauchy
    sineCoefficients sineCoefficientsMajorizedByExponential


cosinePowerSeriesIsAbsolutelyCauchy : ∀ x →
  IsAbsolutelyCauchySeries (powerSeriesTerms cosineCoefficients x)
cosinePowerSeriesIsAbsolutelyCauchy =
  trigonometricPowerSeriesIsAbsolutelyCauchy
    cosineCoefficients cosineCoefficientsMajorizedByExponential


sineCosineTermsCauchyProductHasSum : ∀ x y →
  HasSum
    (cauchyProduct
      (powerSeriesTerms sineCoefficients x)
      (powerSeriesTerms cosineCoefficients y))
    (sinℝ x · cosℝ y)
sineCosineTermsCauchyProductHasSum x y =
  nativeMertensCauchyProductHasSum
    (powerSeriesTerms sineCoefficients x)
    (powerSeriesTerms cosineCoefficients y)
    (sinℝ x) (cosℝ y)
    (sinePowerSeriesIsAbsolutelyCauchy x)
    (absoluteCauchySeriesIsCauchy
      (powerSeriesTerms cosineCoefficients y)
      (cosinePowerSeriesIsAbsolutelyCauchy y))
    (sinePowerSeriesHasSum x)
    (cosinePowerSeriesHasSum y)


cosineSineTermsCauchyProductHasSum : ∀ x y →
  HasSum
    (cauchyProduct
      (powerSeriesTerms cosineCoefficients x)
      (powerSeriesTerms sineCoefficients y))
    (cosℝ x · sinℝ y)
cosineSineTermsCauchyProductHasSum x y =
  nativeMertensCauchyProductHasSum
    (powerSeriesTerms cosineCoefficients x)
    (powerSeriesTerms sineCoefficients y)
    (cosℝ x) (sinℝ y)
    (cosinePowerSeriesIsAbsolutelyCauchy x)
    (absoluteCauchySeriesIsCauchy
      (powerSeriesTerms sineCoefficients y)
      (sinePowerSeriesIsAbsolutelyCauchy y))
    (cosinePowerSeriesHasSum x)
    (sinePowerSeriesHasSum y)


cosineCosineTermsCauchyProductHasSum : ∀ x y →
  HasSum
    (cauchyProduct
      (powerSeriesTerms cosineCoefficients x)
      (powerSeriesTerms cosineCoefficients y))
    (cosℝ x · cosℝ y)
cosineCosineTermsCauchyProductHasSum x y =
  nativeMertensCauchyProductHasSum
    (powerSeriesTerms cosineCoefficients x)
    (powerSeriesTerms cosineCoefficients y)
    (cosℝ x) (cosℝ y)
    (cosinePowerSeriesIsAbsolutelyCauchy x)
    (absoluteCauchySeriesIsCauchy
      (powerSeriesTerms cosineCoefficients y)
      (cosinePowerSeriesIsAbsolutelyCauchy y))
    (cosinePowerSeriesHasSum x)
    (cosinePowerSeriesHasSum y)


sineSineTermsCauchyProductHasSum : ∀ x y →
  HasSum
    (cauchyProduct
      (powerSeriesTerms sineCoefficients x)
      (powerSeriesTerms sineCoefficients y))
    (sinℝ x · sinℝ y)
sineSineTermsCauchyProductHasSum x y =
  nativeMertensCauchyProductHasSum
    (powerSeriesTerms sineCoefficients x)
    (powerSeriesTerms sineCoefficients y)
    (sinℝ x) (sinℝ y)
    (sinePowerSeriesIsAbsolutelyCauchy x)
    (absoluteCauchySeriesIsCauchy
      (powerSeriesTerms sineCoefficients y)
      (sinePowerSeriesIsAbsolutelyCauchy y))
    (sinePowerSeriesHasSum x)
    (sinePowerSeriesHasSum y)


sineAdditionConvolutionTerms : ℝ → ℝ → RealSequence
sineAdditionConvolutionTerms x y n =
  cauchyProduct
      (powerSeriesTerms sineCoefficients x)
      (powerSeriesTerms cosineCoefficients y) n
    +
  cauchyProduct
      (powerSeriesTerms cosineCoefficients x)
      (powerSeriesTerms sineCoefficients y) n


cosineAdditionConvolutionTerms : ℝ → ℝ → RealSequence
cosineAdditionConvolutionTerms x y n =
  cauchyProduct
      (powerSeriesTerms cosineCoefficients x)
      (powerSeriesTerms cosineCoefficients y) n
    -
  cauchyProduct
      (powerSeriesTerms sineCoefficients x)
      (powerSeriesTerms sineCoefficients y) n


sineAdditionConvolutionHasSum : ∀ x y →
  HasSum
    (sineAdditionConvolutionTerms x y)
    ((sinℝ x · cosℝ y) + (cosℝ x · sinℝ y))
sineAdditionConvolutionHasSum x y =
  snd
    (addSummable
      (cauchyProduct
        (powerSeriesTerms sineCoefficients x)
        (powerSeriesTerms cosineCoefficients y))
      (cauchyProduct
        (powerSeriesTerms cosineCoefficients x)
        (powerSeriesTerms sineCoefficients y))
      (sinℝ x · cosℝ y , sineCosineTermsCauchyProductHasSum x y)
      (cosℝ x · sinℝ y , cosineSineTermsCauchyProductHasSum x y))


cosineAdditionConvolutionHasSum : ∀ x y →
  HasSum
    (cosineAdditionConvolutionTerms x y)
    ((cosℝ x · cosℝ y) - (sinℝ x · sinℝ y))
cosineAdditionConvolutionHasSum x y =
  snd
    (subSummable
      (cauchyProduct
        (powerSeriesTerms cosineCoefficients x)
        (powerSeriesTerms cosineCoefficients y))
      (cauchyProduct
        (powerSeriesTerms sineCoefficients x)
        (powerSeriesTerms sineCoefficients y))
      (cosℝ x · cosℝ y , cosineCosineTermsCauchyProductHasSum x y)
      (sinℝ x · sinℝ y , sineSineTermsCauchyProductHasSum x y))


-- The analytic argument is complete once the finite anti-diagonal identity
-- is supplied.  This formulation isolates that purely coefficient-level
-- dependency from Mertens convergence and uniqueness of series sums.

sineAddHasAdditionSumFromConvolution : ∀ x y →
  sineAdditionConvolutionTerms x y
    ≡ powerSeriesTerms sineCoefficients (x + y) →
  HasSum
    (powerSeriesTerms sineCoefficients (x + y))
    ((sinℝ x · cosℝ y) + (cosℝ x · sinℝ y))
sineAddHasAdditionSumFromConvolution x y convolution-path =
  subst
    (λ terms →
      HasSum terms
        ((sinℝ x · cosℝ y) + (cosℝ x · sinℝ y)))
    convolution-path
    (sineAdditionConvolutionHasSum x y)


cosineAddHasAdditionSumFromConvolution : ∀ x y →
  cosineAdditionConvolutionTerms x y
    ≡ powerSeriesTerms cosineCoefficients (x + y) →
  HasSum
    (powerSeriesTerms cosineCoefficients (x + y))
    ((cosℝ x · cosℝ y) - (sinℝ x · sinℝ y))
cosineAddHasAdditionSumFromConvolution x y convolution-path =
  subst
    (λ terms →
      HasSum terms
        ((cosℝ x · cosℝ y) - (sinℝ x · sinℝ y)))
    convolution-path
    (cosineAdditionConvolutionHasSum x y)


sinℝ-add-from-convolution : ∀ x y →
  sineAdditionConvolutionTerms x y
    ≡ powerSeriesTerms sineCoefficients (x + y) →
  sinℝ (x + y)
    ≡ (sinℝ x · cosℝ y) + (cosℝ x · sinℝ y)
sinℝ-add-from-convolution x y convolution-path =
  seriesSumIndependent
    (powerSeriesTerms sineCoefficients (x + y))
    (sinℝ (x + y) , sinePowerSeriesHasSum (x + y))
    ( (sinℝ x · cosℝ y) + (cosℝ x · sinℝ y)
    , sineAddHasAdditionSumFromConvolution x y convolution-path)


cosℝ-add-from-convolution : ∀ x y →
  cosineAdditionConvolutionTerms x y
    ≡ powerSeriesTerms cosineCoefficients (x + y) →
  cosℝ (x + y)
    ≡ (cosℝ x · cosℝ y) - (sinℝ x · sinℝ y)
cosℝ-add-from-convolution x y convolution-path =
  seriesSumIndependent
    (powerSeriesTerms cosineCoefficients (x + y))
    (cosℝ (x + y) , cosinePowerSeriesHasSum (x + y))
    ( (cosℝ x · cosℝ y) - (sinℝ x · sinℝ y)
    , cosineAddHasAdditionSumFromConvolution x y convolution-path)

module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (addInvR)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.Product.Native
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.AtZero
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition.Finite


exponentialEntirePowerSeriesHasSum : ∀ x →
  HasSum (powerSeriesTerms exponentialCoefficients x) (exponentialEntireValue x)
exponentialEntirePowerSeriesHasSum x =
  seriesSumHasSum
    (powerSeriesTerms exponentialCoefficients x)
    (entirePowerSeriesSummableAt
      exponentialCoefficients exponentialPowerSeriesEntireUniformlyCauchy x)


opaque
  exponentialEntireValue-zero : exponentialEntireValue 0ℝ ≡ 1ℝ
  exponentialEntireValue-zero =
    powerSeriesValueAtZero exponentialCoefficients
      (entirePowerSeriesSummableAt
        exponentialCoefficients exponentialPowerSeriesEntireUniformlyCauchy 0ℝ)
    ∙ exponentialCoefficients-zero

  exponentialAdditionHasSum : ∀ x y →
    HasSum (powerSeriesTerms exponentialCoefficients (x + y))
      (exponentialEntireValue x · exponentialEntireValue y)
  exponentialAdditionHasSum x y =
    subst
      (λ terms → HasSum terms (exponentialEntireValue x · exponentialEntireValue y))
      (exponentialAdditionConvolutionTerms x y)
      (nativeMertensCauchyProductHasSum
        (powerSeriesTerms exponentialCoefficients x)
        (powerSeriesTerms exponentialCoefficients y)
        (exponentialEntireValue x) (exponentialEntireValue y)
        (exponentialPowerSeriesIsAbsolutelyCauchyEverywhere x)
        (absoluteCauchySeriesIsCauchy
          (powerSeriesTerms exponentialCoefficients y)
          (exponentialPowerSeriesIsAbsolutelyCauchyEverywhere y))
        (exponentialEntirePowerSeriesHasSum x)
        (exponentialEntirePowerSeriesHasSum y))

  exponentialEntireValue-add : ∀ x y →
    exponentialEntireValue (x + y) ≡
    exponentialEntireValue x · exponentialEntireValue y
  exponentialEntireValue-add x y =
    seriesSumIndependent
      (powerSeriesTerms exponentialCoefficients (x + y))
      (exponentialEntireValue (x + y) , exponentialEntirePowerSeriesHasSum (x + y))
      (exponentialEntireValue x · exponentialEntireValue y , exponentialAdditionHasSum x y)

  exponentialEntireValue-mul-negative : ∀ x →
    exponentialEntireValue x · exponentialEntireValue (- x) ≡ 1ℝ
  exponentialEntireValue-mul-negative x =
    sym (exponentialEntireValue-add x (- x))
    ∙ cong exponentialEntireValue (addInvR x)
    ∙ exponentialEntireValue-zero

module Cubical.Analysis.Complex.Series.PowerSeries.Exponential.HasSum where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negZero)
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Functions.Exponential using (expℝ)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Polar.Cis
import Cubical.Analysis.Complex.Polar.Algebra as Polar
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Absolute
open import Cubical.Analysis.Complex.Series.Product.Finite
open import Cubical.Analysis.Complex.Series.Product.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Exponential.Finite
open import Cubical.Analysis.Complex.Series.PowerSeries.Exponential.Imaginary

private module A = Polar.PolarAlgebra ℝCommRing

-- The finite binomial identity and the native Mertens theorem lift any two
-- known sums to the sum at the added argument.
opaque
  exponentialComplexSeriesAdditionHasSum : ∀ z w x y →
    HasComplexSum (powerSeriesTermsℂ exponentialCoefficientsℂ z) x →
    HasComplexSum (powerSeriesTermsℂ exponentialCoefficientsℂ w) y →
    HasComplexSum (powerSeriesTermsℂ exponentialCoefficientsℂ (z +ℂ w)) (x ·ℂ y)
  exponentialComplexSeriesAdditionHasSum z w x y first second = complexHasSumPointwise
    (cauchyProductℂ (powerSeriesTermsℂ exponentialCoefficientsℂ z) (powerSeriesTermsℂ exponentialCoefficientsℂ w))
    (powerSeriesTermsℂ exponentialCoefficientsℂ (z +ℂ w))
    (exponentialAdditionConvolutionℂTerm z w) (x ·ℂ y)
    (mertensCauchyProductℂHasSum
      (powerSeriesTermsℂ exponentialCoefficientsℂ z) (powerSeriesTermsℂ exponentialCoefficientsℂ w) x y
      (exponentialComplexSeriesIsAbsolutelyCauchy z)
      (absoluteComplexCauchySeriesIsCauchy (powerSeriesTermsℂ exponentialCoefficientsℂ w)
        (exponentialComplexSeriesIsAbsolutelyCauchy w)) first second)

private
  opaque
    splitCoordinates : ∀ z → fromℝ (re z) +ℂ iℂ ·ℂ fromℝ (im z) ≡ z
    splitCoordinates z = cong (fromℝ (re z) +ℂ_)
      (A.quarterRotate (im z) 0ℝ ∙ ℂ≡ negZero refl)
      ∙ ℂ≡ (addIdR (re z)) (addIdL (im z))

-- This is an identification of the existing polar exponential with its
-- standard complex series, not a second definition of the function.
opaque
  exponentialComplexPowerSeriesHasSum : ∀ z →
    HasComplexSum (powerSeriesTermsℂ exponentialCoefficientsℂ z) (expℂ z)
  exponentialComplexPowerSeriesHasSum z =
    subst (HasComplexSum (powerSeriesTermsℂ exponentialCoefficientsℂ z)) (sym (expℂ-polar z))
      (subst (λ w → HasComplexSum (powerSeriesTermsℂ exponentialCoefficientsℂ w)
          (polarℂ (expℝ (re z)) (im z))) (splitCoordinates z)
        (exponentialComplexSeriesAdditionHasSum (fromℝ (re z)) (iℂ ·ℂ fromℝ (im z))
          (fromℝ (expℝ (re z))) (cisℝ (im z))
          (exponentialComplexSeriesHasSumReal (re z)) (exponentialComplexSeriesHasSumImaginary (im z))))

exponentialComplexPowerSeriesSummable : ∀ z → ComplexSummable (powerSeriesTermsℂ exponentialCoefficientsℂ z)
exponentialComplexPowerSeriesSummable z = expℂ z , exponentialComplexPowerSeriesHasSum z

exponentialComplexPowerSeriesValue : ∀ z (summable : ComplexSummable (powerSeriesTermsℂ exponentialCoefficientsℂ z)) →
  seriesSumℂ (powerSeriesTermsℂ exponentialCoefficientsℂ z) summable ≡ expℂ z
exponentialComplexPowerSeriesValue z summable = complexSumUnique
  (powerSeriesTermsℂ exponentialCoefficientsℂ z) (fst summable) (expℂ z)
  (snd summable) (exponentialComplexPowerSeriesHasSum z)

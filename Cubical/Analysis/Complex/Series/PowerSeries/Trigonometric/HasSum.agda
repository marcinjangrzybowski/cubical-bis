module Cubical.Analysis.Complex.Series.PowerSeries.Trigonometric.HasSum where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Constants
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Operations
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Exponential.HasSum
open import Cubical.Analysis.Complex.Series.PowerSeries.Trigonometric.Finite

private
  opaque
    negativeImaginaryExponentialHasSum : ∀ z →
      HasComplexSum (powerSeriesTermsℂ exponentialCoefficientsℂ ((-ℂ iℂ) ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))
    negativeImaginaryExponentialHasSum z =
      subst (HasComplexSum (powerSeriesTermsℂ exponentialCoefficientsℂ ((-ℂ iℂ) ·ℂ z)))
        (cong expℂ (ℂRing.-DistL· iℂ z)) (exponentialComplexPowerSeriesHasSum ((-ℂ iℂ) ·ℂ z))

-- Linearity of the existing series sums transfers the finite Euler identities.
-- These theorems identify the existing sine/cosine; their definitions stay fixed.
opaque
  cosineComplexPowerSeriesHasSum : ∀ z →
    HasComplexSum (powerSeriesTermsℂ cosineCoefficientsℂ z) (cosℂ z)
  cosineComplexPowerSeriesHasSum z =
    subst (HasComplexSum (powerSeriesTermsℂ cosineCoefficientsℂ z)) (sym (cosℂ-exp z))
      (complexHasSumPointwise
        (λ n → cosFromExp (powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ z) n)
          (powerSeriesTermsℂ exponentialCoefficientsℂ ((-ℂ iℂ) ·ℂ z) n))
        (powerSeriesTermsℂ cosineCoefficientsℂ z) (cosineExponentialTermsℂ z)
        (cosFromExp (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z))))
        (scaleHasComplexSum halfℂ
          (λ n → powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ z) n
            +ℂ powerSeriesTermsℂ exponentialCoefficientsℂ ((-ℂ iℂ) ·ℂ z) n)
          (expℂ (iℂ ·ℂ z) +ℂ expℂ (-ℂ (iℂ ·ℂ z)))
          (addHasComplexSum
            (powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ z))
            (powerSeriesTermsℂ exponentialCoefficientsℂ ((-ℂ iℂ) ·ℂ z))
            (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))
            (exponentialComplexPowerSeriesHasSum (iℂ ·ℂ z)) (negativeImaginaryExponentialHasSum z))))

  sineComplexPowerSeriesHasSum : ∀ z →
    HasComplexSum (powerSeriesTermsℂ sineCoefficientsℂ z) (sinℂ z)
  sineComplexPowerSeriesHasSum z =
    subst (HasComplexSum (powerSeriesTermsℂ sineCoefficientsℂ z)) (sym (sinℂ-exp z))
      (complexHasSumPointwise
        (λ n → sinFromExp (powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ z) n)
          (powerSeriesTermsℂ exponentialCoefficientsℂ ((-ℂ iℂ) ·ℂ z) n))
        (powerSeriesTermsℂ sineCoefficientsℂ z) (sineExponentialTermsℂ z)
        (sinFromExp (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z))))
        (scaleHasComplexSum ((-ℂ iℂ) ·ℂ halfℂ)
          (λ n → powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ z) n
            -ℂ powerSeriesTermsℂ exponentialCoefficientsℂ ((-ℂ iℂ) ·ℂ z) n)
          (expℂ (iℂ ·ℂ z) -ℂ expℂ (-ℂ (iℂ ·ℂ z)))
          (subHasComplexSum
            (powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ z))
            (powerSeriesTermsℂ exponentialCoefficientsℂ ((-ℂ iℂ) ·ℂ z))
            (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))
            (exponentialComplexPowerSeriesHasSum (iℂ ·ℂ z)) (negativeImaginaryExponentialHasSum z))))

cosineComplexPowerSeriesSummable : ∀ z → ComplexSummable (powerSeriesTermsℂ cosineCoefficientsℂ z)
cosineComplexPowerSeriesSummable z = cosℂ z , cosineComplexPowerSeriesHasSum z

sineComplexPowerSeriesSummable : ∀ z → ComplexSummable (powerSeriesTermsℂ sineCoefficientsℂ z)
sineComplexPowerSeriesSummable z = sinℂ z , sineComplexPowerSeriesHasSum z

cosineComplexPowerSeriesValue : ∀ z (summable : ComplexSummable (powerSeriesTermsℂ cosineCoefficientsℂ z)) →
  seriesSumℂ (powerSeriesTermsℂ cosineCoefficientsℂ z) summable ≡ cosℂ z
cosineComplexPowerSeriesValue z summable = complexSumUnique
  (powerSeriesTermsℂ cosineCoefficientsℂ z) (fst summable) (cosℂ z)
  (snd summable) (cosineComplexPowerSeriesHasSum z)

sineComplexPowerSeriesValue : ∀ z (summable : ComplexSummable (powerSeriesTermsℂ sineCoefficientsℂ z)) →
  seriesSumℂ (powerSeriesTermsℂ sineCoefficientsℂ z) summable ≡ sinℂ z
sineComplexPowerSeriesValue z summable = complexSumUnique
  (powerSeriesTermsℂ sineCoefficientsℂ z) (fst summable) (sinℂ z)
  (snd summable) (sineComplexPowerSeriesHasSum z)

-- These sum equations are the inputs expected by the general power-series
-- differentiation and line-integral theorems.
sineFormalDerivativeHasComplexSum : ∀ z →
  HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ sineCoefficientsℂ) z) (cosℂ z)
sineFormalDerivativeHasComplexSum z =
  subst (λ coefficients → HasComplexSum (powerSeriesTermsℂ coefficients z) (cosℂ z))
    (sym formalDerivativeℂ-sine) (cosineComplexPowerSeriesHasSum z)

opaque
  cosineFormalDerivativeHasComplexSum : ∀ z →
    HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ cosineCoefficientsℂ) z) (-ℂ sinℂ z)
  cosineFormalDerivativeHasComplexSum z = complexHasSumPointwise
    (λ n → -ℂ powerSeriesTermsℂ sineCoefficientsℂ z n)
    (powerSeriesTermsℂ (formalDerivativeℂ cosineCoefficientsℂ) z)
    (λ n → sym (cong (_·ℂ (z ^ℂ n)) (funExt⁻ formalDerivativeℂ-cosine n)
      ∙ ℂRing.-DistL· (sineCoefficientsℂ n) (z ^ℂ n))) (-ℂ sinℂ z)
    (negHasComplexSum (powerSeriesTermsℂ sineCoefficientsℂ z) (sinℂ z) (sineComplexPowerSeriesHasSum z))

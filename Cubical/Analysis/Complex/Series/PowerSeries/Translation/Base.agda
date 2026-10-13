module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as Nat
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.Strict.Base
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.PowerSeries.RepeatedDerivative as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Operations
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Coefficients
import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Algebra as Algebra

private module A = Algebra.TranslationAlgebra ℂCommRing

-- Row n is the binomial series for the n-th coefficient at the new center.
-- Its source coefficient is a[k+n], with the original degree recovered on
-- each finite anti-diagonal.
translatedCoefficientTermsℂ : ComplexSequence → ℂ → ℕ → ComplexSequence
translatedCoefficientTermsℂ coefficients center order index =
  (binomialCoefficientℂ (index Nat.+ order) order ·ℂ coefficients (index Nat.+ order)) ·ℂ (center ^ℂ index)

opaque
  translatedCoefficientTermℂ-normalized : ∀ coefficients center order index →
    exponentialCoefficientsℂ order ·ℂ powerSeriesTermsℂ (repeatedFormalDerivativeℂ order coefficients) center index
      ≡ translatedCoefficientTermsℂ coefficients center order index
  translatedCoefficientTermℂ-normalized coefficients center order index =
    cong (λ value → exponentialCoefficientsℂ order ·ℂ (value ·ℂ (center ^ℂ index)))
      (repeatedFormalDerivativeℂ-coefficient order coefficients index)
    ∙ A.normalizeDerivativeTerm (exponentialCoefficientsℂ order)
        (fromℝ (realNatural (Real.derivativeNaturalProduct index order)))
        (coefficients (index Nat.+ order)) (center ^ℂ index)
    ∙ cong (λ multiplier → (multiplier ·ℂ coefficients (index Nat.+ order)) ·ℂ (center ^ℂ index))
        (normalizedDerivativeMultiplierℂ order index)

-- Every individual translated coefficient is already a constructed sum;
-- convergence of the whole reexpanded power series is a further theorem.
translatedCoefficientTermsℂHasSum : ∀ (coefficients : ComplexSequence) (outer : ℝ)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
  (center : ℂ) (inside : normℂ center <ℝ outer) (order : ℕ) →
  HasComplexSum (translatedCoefficientTermsℂ coefficients center order)
    (complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside order)
translatedCoefficientTermsℂHasSum coefficients outer witness center inside order = complexHasSumPointwise
  (scaleComplexSeries (exponentialCoefficientsℂ order) (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order coefficients) center))
  (translatedCoefficientTermsℂ coefficients center order) (translatedCoefficientTermℂ-normalized coefficients center order)
  (complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside order)
  (complexPowerSeriesTaylorCoefficientAtCenterHasSum coefficients outer witness center inside order)

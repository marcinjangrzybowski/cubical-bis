module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Reflection where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Order.Strict.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Interior
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Canonical

-- Reexpansion reflects represented values as well as preserving them.
-- Compare with the constructed original sum rather than reversing an
-- infinite rearrangement or extracting any additional convergence data.
opaque
  translatedTaylorReflectsHasSum : ∀ (coefficients : ComplexSequence) (outer : ℝ)
    (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
    (center : ℂ) (inside : normℂ center <ℝ outer) increment →
    normℂ center + normℂ increment <ℝ outer → ∀ value →
    HasComplexSum (powerSeriesTermsℂ
      (complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside) increment) value →
    HasComplexSum (powerSeriesTermsℂ coefficients (center +ℂ increment)) value
  translatedTaylorReflectsHasSum coefficients outer witness center inside increment fits value localSum =
    subst (HasComplexSum (powerSeriesTermsℂ coefficients (center +ℂ increment)))
      (complexSumUnique (powerSeriesTermsℂ translated increment) canonical value
        (translatedTaylorHasCanonicalSum coefficients outer witness center inside increment fits) localSum)
      (openInteriorPowerSeriesDerivativeSums coefficients outer witness 0 point)
    where
    translated : ComplexSequence
    translated = complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside
    point : OpenComplexNormRadius outer
    point = center +ℂ increment , translatedEvaluationInside center increment outer fits
    canonical : ℂ
    canonical = openInteriorPowerSeriesDerivatives coefficients outer witness 0 point

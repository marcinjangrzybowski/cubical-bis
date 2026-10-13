module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Canonical where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Interior
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Representation

translatedEvaluationInside : ∀ center increment outer →
  normℂ center + normℂ increment <ℝ outer → normℂ (center +ℂ increment) <ℝ outer
translatedEvaluationInside center increment outer fits = ≤<ℝ-trans
  (normℂ (center +ℂ increment)) (normℂ center + normℂ increment) outer
  (normℂ-triangle center increment) fits

-- No additional representation premise: the target is the already
-- constructed order-zero sum of the original native power series.
opaque
  translatedTaylorHasCanonicalSum : ∀ (coefficients : ComplexSequence) (outer : ℝ)
    (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
    (center : ℂ) (inside : normℂ center <ℝ outer) increment
    (fits : normℂ center + normℂ increment <ℝ outer) →
    HasComplexSum (powerSeriesTermsℂ
      (complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside) increment)
      (openInteriorPowerSeriesDerivatives coefficients outer witness 0
        (center +ℂ increment , translatedEvaluationInside center increment outer fits))
  translatedTaylorHasCanonicalSum coefficients outer witness center inside increment fits =
    translatedTaylorHasSum coefficients outer witness center inside increment fits
      (openInteriorPowerSeriesDerivatives coefficients outer witness 0 point)
      (openInteriorPowerSeriesDerivativeSums coefficients outer witness 0 point)
    where
    point : OpenComplexNormRadius outer
    point = center +ℂ increment , translatedEvaluationInside center increment outer fits

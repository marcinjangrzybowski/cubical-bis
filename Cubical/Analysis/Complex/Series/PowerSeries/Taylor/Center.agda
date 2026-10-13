module Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Strict.Base
import Cubical.Analysis.Real.Series.Base as Real
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
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Interior
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Coefficients

-- Canonical Taylor coefficients at an arbitrary interior center, formed
-- from the actual derivative tower on the whole open convergence ball.
-- Their existence does not yet assert convergence of the reexpanded series.
complexPowerSeriesTaylorCoefficientsAtCenter : ∀ coefficients outer →
  Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) →
  ∀ center → normℂ center <ℝ outer → ComplexSequence
complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside =
  taylorCoefficientsℂ (λ n → openInteriorPowerSeriesDerivatives coefficients outer witness n (center , inside))

-- The n-th translated coefficient is the sum of the normalized n-th formal
-- derivative series. This uses existing native factorial multipliers and
-- converges from the original outer witness, with no new choice principle.
complexPowerSeriesTaylorCoefficientAtCenterHasSum : ∀ (coefficients : ComplexSequence) (outer : ℝ)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
  (center : ℂ) (inside : normℂ center <ℝ outer) (n : ℕ) →
  HasComplexSum (scaleComplexSeries (exponentialCoefficientsℂ n)
    (powerSeriesTermsℂ (repeatedFormalDerivativeℂ n coefficients) center))
    (complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside n)
complexPowerSeriesTaylorCoefficientAtCenterHasSum coefficients outer witness center inside n =
  scaleHasComplexSum (exponentialCoefficientsℂ n) (powerSeriesTermsℂ (repeatedFormalDerivativeℂ n coefficients) center)
    (openInteriorPowerSeriesDerivatives coefficients outer witness n (center , inside))
    (openInteriorPowerSeriesDerivativeSums coefficients outer witness n (center , inside))

opaque
  complexPowerSeriesTaylorCoefficientsAtCenterIndependent : ∀ (coefficients : ComplexSequence) (firstOuter secondOuter : ℝ)
    (firstWitness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients firstOuter))
    (secondWitness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients secondOuter))
    (center : ℂ) (firstInside : normℂ center <ℝ firstOuter) (secondInside : normℂ center <ℝ secondOuter) →
    complexPowerSeriesTaylorCoefficientsAtCenter coefficients firstOuter firstWitness center firstInside ≡
    complexPowerSeriesTaylorCoefficientsAtCenter coefficients secondOuter secondWitness center secondInside
  complexPowerSeriesTaylorCoefficientsAtCenterIndependent coefficients firstOuter secondOuter
    firstWitness secondWitness center firstInside secondInside = funExt λ n → cong (exponentialCoefficientsℂ n ·ℂ_)
      (openInteriorPowerSeriesDerivativeAgrees coefficients firstOuter firstWitness n (center , firstInside)
        (openInteriorPowerSeriesDerivatives coefficients secondOuter secondWitness n (center , secondInside))
        (openInteriorPowerSeriesDerivativeSums coefficients secondOuter secondWitness n (center , secondInside)))

  complexPowerSeriesTaylorCoefficientsAtOrigin : ∀ (coefficients : ComplexSequence) (outer : ℝ)
    (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer)) (positive : 0ℝ <ℝ outer) →
    complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness 0ℂ
      (subst (_<ℝ outer) (sym normℂ-zero) positive) ≡ coefficients
  complexPowerSeriesTaylorCoefficientsAtOrigin coefficients outer witness positive =
    complexPowerSeriesTaylorCoefficients coefficients
      (λ n → openInteriorPowerSeriesDerivatives coefficients outer witness n
        (0ℂ , subst (_<ℝ outer) (sym normℂ-zero) positive))
      (λ n → openInteriorPowerSeriesDerivativeSums coefficients outer witness n
        (0ℂ , subst (_<ℝ outer) (sym normℂ-zero) positive))

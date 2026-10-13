module Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Properties
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Absolute as Real
import Cubical.Analysis.Real.Series.Operations as Real
import Cubical.Analysis.Real.Series.Successor as Real
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Bounds

private
  majorantNonnegative : ∀ coefficients radius → 0ℝ ≤ℝ radius → ∀ n →
    0ℝ ≤ℝ complexPowerSeriesMajorant coefficients radius n
  majorantNonnegative coefficients radius nonnegative n =
    isNonnegative→0≤ (complexPowerSeriesMajorant coefficients radius n)
      (mulPresIsNonnegative (normℂ (coefficients n)) (powℝ radius n)
        (0≤→isNonnegative (normℂ (coefficients n)) (normℂ-nonnegative (coefficients n)))
        (powPresIsNonnegative radius n (0≤→isNonnegative radius nonnegative)))

-- The primitive converges natively at the SAME nonnegative radius. A single
-- rational upper bound on that radius supplies a scaled tail majorant; the
-- initial constant is restored with an explicit successor modulus.
opaque
  formalPrimitiveℂMajorantIsCauchy : ∀ constant coefficients radius → 0ℝ ≤ℝ radius →
    Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius) →
    Real.IsCauchySeries (complexPowerSeriesMajorant (formalPrimitiveℂ constant coefficients) radius)
  formalPrimitiveℂMajorantIsCauchy constant coefficients radius nonnegative witness =
    Real.successorSeriesReflectsIsCauchy primitiveMajorant
      (PT.rec (Real.isPropIsCauchySeries (λ n → primitiveMajorant (suc n)))
        (λ { (bound , below) → Real.dominatedCauchySeriesIsCauchy
          (λ n → primitiveMajorant (suc n)) (Real.scaleSeries (rat (naturalRational bound)) originalMajorant)
          (λ n → subst (_≤ℝ rat (naturalRational bound) · originalMajorant n)
            (sym (absOfNonnegative (primitiveMajorant (suc n))
              (majorantNonnegative (formalPrimitiveℂ constant coefficients) radius nonnegative (suc n))))
            (≤ℝ-trans (primitiveMajorant (suc n)) (radius · originalMajorant n)
              (rat (naturalRational bound) · originalMajorant n)
              (formalPrimitiveℂMajorantStepBound constant coefficients radius nonnegative n)
              (mulPres≤R-0≤ radius (rat (naturalRational bound)) (originalMajorant n)
                (majorantNonnegative coefficients radius nonnegative n)
                (<ℝ-weaken radius (rat (naturalRational bound)) below))))
          (Real.rationalScaleSeriesIsCauchy (naturalRational bound) originalMajorant witness) })
        (∃naturalUpperBound radius))
    where
    originalMajorant primitiveMajorant : Real.RealSequence
    originalMajorant = complexPowerSeriesMajorant coefficients radius
    primitiveMajorant = complexPowerSeriesMajorant (formalPrimitiveℂ constant coefficients) radius

  formalPrimitiveℂDerivativeMajorantIsCauchy : ∀ constant coefficients radius →
    Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius) →
    Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant (formalPrimitiveℂ constant coefficients) radius)
  formalPrimitiveℂDerivativeMajorantIsCauchy constant coefficients radius =
    subst Real.IsCauchySeries (sym (formalPrimitiveℂDerivativeMajorant constant coefficients radius))

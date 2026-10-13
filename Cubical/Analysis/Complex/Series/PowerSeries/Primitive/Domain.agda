module Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Domain where

open import Cubical.Foundations.Prelude
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Uniform
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform

-- Intrinsic values on the closed convergence norm ball. Uniform derivatives
-- here concern chords within that domain, including its boundary; they do
-- not assert the existence of an ambient derivative at boundary points.
module _ (coefficients : ComplexSequence) (radius : ℝ)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius)) where

  opaque
    closedComplexPowerSeriesValue : ClosedComplexNormRadius radius → ℂ
    closedComplexPowerSeriesValue = uniformComplexPowerSeriesValue fst coefficients radius snd witness

    closedComplexPowerSeriesHasSum : ∀ point →
      HasComplexSum (powerSeriesTermsℂ coefficients (fst point)) (closedComplexPowerSeriesValue point)
    closedComplexPowerSeriesHasSum = uniformHasComplexSumAt
      (uniformComplexPowerSeriesHasSum fst coefficients radius snd witness)

  module _ (constant : ℂ) (nonnegative : 0ℝ ≤ℝ radius) where
    closedComplexPowerSeriesPrimitive : ClosedComplexNormRadius radius → ℂ
    closedComplexPowerSeriesPrimitive = uniformComplexPowerSeriesPrimitive fst constant coefficients radius nonnegative snd witness

    closedComplexPowerSeriesPrimitiveHasSum : ∀ point →
      HasComplexSum (powerSeriesTermsℂ (formalPrimitiveℂ constant coefficients) (fst point))
        (closedComplexPowerSeriesPrimitive point)
    closedComplexPowerSeriesPrimitiveHasSum =
      uniformComplexPowerSeriesPrimitiveHasSum fst constant coefficients radius nonnegative snd witness

    closedComplexPowerSeriesPrimitiveAtZero :
      closedComplexPowerSeriesPrimitive (0ℂ , subst (_≤ℝ radius) (sym normℂ-zero) nonnegative) ≡ constant
    closedComplexPowerSeriesPrimitiveAtZero = uniformComplexPowerSeriesPrimitiveAtZero fst constant coefficients radius nonnegative snd witness
      (0ℂ , subst (_≤ℝ radius) (sym normℂ-zero) nonnegative) refl

    opaque
      unfolding closedComplexPowerSeriesValue

      closedComplexPowerSeriesPrimitiveHasUniformDerivative :
        IsRadiuswiseUniformComplexDerivativeAlong (ClosedComplexNormRadiusPremetricSpace radius .snd) fst
          closedComplexPowerSeriesPrimitive closedComplexPowerSeriesValue
      closedComplexPowerSeriesPrimitiveHasUniformDerivative =
        uniformComplexPowerSeriesPrimitiveHasDerivativeAlong fst constant coefficients radius nonnegative snd witness
          (ClosedComplexNormRadiusPremetricSpace radius .snd) (λ ε → PT.∣ ε , (λ x y close → close) ∣₁)

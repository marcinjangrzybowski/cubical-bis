module Cubical.Analysis.Complex.Series.PowerSeries.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Series.Base using (RealSequence)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
import Cubical.Analysis.Complex.Series.PowerSeries.Bounds.NormPower as Bound

opaque
  complexPowerNormBound : ∀ z n → normℂ (z ^ℂ n) ≤ℝ powℝ (normℂ z) n
  complexPowerNormBound = Bound.NormPower.powerBound ℂCommRing normℂ normℂ-one
    normℂ-nonnegative normℂ-submultiplicative

opaque
  complexPowerNormBoundOn : ∀ z radius → normℂ z ≤ℝ radius → ∀ n → normℂ (z ^ℂ n) ≤ℝ powℝ radius n
  complexPowerNormBoundOn z radius bounded n = ≤ℝ-trans (normℂ (z ^ℂ n)) (powℝ (normℂ z) n) (powℝ radius n)
    (complexPowerNormBound z n) (powMono {x = normℂ z} {y = radius} n (normℂ-nonnegative z) bounded)

-- The real comparison series at one supplied l1 radius.
complexPowerSeriesMajorant : ComplexSequence → ℝ → RealSequence
complexPowerSeriesMajorant coefficients radius n = normℂ (coefficients n) · powℝ radius n

opaque
  complexPowerSeriesTermBound : ∀ coefficients z radius → normℂ z ≤ℝ radius →
    ∀ n → normℂ (powerSeriesTermsℂ coefficients z n) ≤ℝ complexPowerSeriesMajorant coefficients radius n
  complexPowerSeriesTermBound coefficients z radius bounded n = normℂ-mulBound
    (coefficients n) (z ^ℂ n) (normℂ (coefficients n)) (powℝ radius n)
    (≤ℝ-refl (normℂ (coefficients n))) (complexPowerNormBoundOn z radius bounded n)

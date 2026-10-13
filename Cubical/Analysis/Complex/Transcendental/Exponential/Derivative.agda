module Cubical.Analysis.Complex.Transcendental.Exponential.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Functions.Exponential.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Holomorphic
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Derivative.Separated

private
  opaque
    expℂ-separated : ∀ z → expℂ z ≡ separatedExponential expℝ cosℝ sinℝ z
    expℂ-separated z = expℂ-polar z
      ∙ cong (fromℝ (expℝ (re z)) ·ℂ_) (cisℝ-value (im z))
      ∙ sym (separatedExponential-value expℝ cosℝ sinℝ z)

opaque
  -- A complex-linear derivative, not just differentiation on the real axis.
  -- The proof reuses the three native real derivative theorems and controls
  -- both coordinate increments by the complex l1 norm.
  expℂHasSelfDerivative : IsComplexDerivative expℂ expℂ
  expℂHasSelfDerivative = subst (λ f → IsComplexDerivative f f)
    (sym (funExt expℂ-separated))
    (separatedExponentialHasSelfDerivative expℝ cosℝ sinℝ
      exponentialHasSelfDerivative cosℝHasDerivative sinℝHasDerivative)

  expℂ-isEntire : IsEntire expℂ
  expℂ-isEntire = complexDerivativeGivesEntire expℂ expℂ expℂHasSelfDerivative

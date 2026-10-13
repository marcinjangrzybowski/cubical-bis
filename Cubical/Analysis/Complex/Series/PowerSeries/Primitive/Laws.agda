module Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (zero; suc)
import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Primitive as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Base

-- The existing real inverse law gives coefficient recovery without division
-- by an arbitrary complex number. No analytic hypotheses are involved.
opaque
  formalPrimitiveℂ-formalDerivativeℂ : ∀ coefficients →
    formalPrimitiveℂ (coefficients zero) (formalDerivativeℂ coefficients) ≡ coefficients
  formalPrimitiveℂ-formalDerivativeℂ coefficients =
    cong (formalPrimitiveℂ (coefficients zero)) (sym (repeatedFormalDerivativeℂ-successor zero coefficients))
    ∙ funExt (λ n → ℂ≡
      (funExt⁻ (Real.formalPrimitive-formalDerivative (re ∘ coefficients)) n)
      (funExt⁻ (Real.formalPrimitive-formalDerivative (im ∘ coefficients)) n))

  formalPrimitiveℂ-unique : ∀ constant coefficients candidate →
    candidate zero ≡ constant → formalDerivativeℂ candidate ≡ coefficients →
    candidate ≡ formalPrimitiveℂ constant coefficients
  formalPrimitiveℂ-unique constant coefficients candidate head derivative =
    sym (formalPrimitiveℂ-formalDerivativeℂ candidate) ∙ cong₂ formalPrimitiveℂ head derivative

  repeatedFormalDerivativeℂ-formalPrimitiveℂ : ∀ order constant coefficients →
    repeatedFormalDerivativeℂ (suc order) (formalPrimitiveℂ constant coefficients) ≡
    repeatedFormalDerivativeℂ order coefficients
  repeatedFormalDerivativeℂ-formalPrimitiveℂ order constant coefficients =
    repeatedFormalDerivativeℂ-commute order (formalPrimitiveℂ constant coefficients)
    ∙ cong (repeatedFormalDerivativeℂ order) (formalDerivativeℂ-formalPrimitiveℂ constant coefficients)

module Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Primitive as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative

-- Use the existing rational division by n+1 in each real coordinate.
-- The initial coefficient is an arbitrary integration constant.
formalPrimitiveℂ : ℂ → ComplexSequence → ComplexSequence
formalPrimitiveℂ constant coefficients n =
  Real.formalPrimitive (re constant) (re ∘ coefficients) n ,
  Real.formalPrimitive (im constant) (im ∘ coefficients) n

opaque
  formalDerivativeℂ-formalPrimitiveℂ : ∀ constant coefficients →
    formalDerivativeℂ (formalPrimitiveℂ constant coefficients) ≡ coefficients
  formalDerivativeℂ-formalPrimitiveℂ constant coefficients =
    sym (repeatedFormalDerivativeℂ-successor 0 (formalPrimitiveℂ constant coefficients))
    ∙ funExt (λ n → ℂ≡
      (funExt⁻ (Real.formalDerivative-formalPrimitive (re constant) (re ∘ coefficients)) n)
      (funExt⁻ (Real.formalDerivative-formalPrimitive (im constant) (im ∘ coefficients)) n))

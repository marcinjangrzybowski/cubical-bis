module Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Translation.Coefficients where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Interior
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Laws
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Domain

-- Reexpanding a primitive equals integrating the reexpanded coefficients.
-- Its new constant MUST be the old primitive's value at the new center.
-- This is a coefficient theorem; convergence of the translated series is
-- supplied separately by the existing strict-interior translation theorem.
module _ (coefficients : ComplexSequence) (outer : ℝ) (nonnegative : 0ℝ ≤ℝ outer)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
  (constant center : ℂ) (inside : normℂ center <ℝ outer) where
  private
    integrated : ComplexSequence
    integrated = formalPrimitiveℂ constant coefficients
    native : Real.IsCauchySeries (complexPowerSeriesMajorant integrated outer)
    native = formalPrimitiveℂMajorantIsCauchy constant coefficients outer nonnegative witness
    point : OpenComplexNormRadius outer
    point = center , inside
    originalDerivatives integratedDerivatives : ℕ → ℂ
    originalDerivatives n = openInteriorPowerSeriesDerivatives coefficients outer witness n point
    integratedDerivatives n = openInteriorPowerSeriesDerivatives integrated outer native n point

  translatedPrimitiveConstant : ℂ
  translatedPrimitiveConstant = closedComplexPowerSeriesPrimitive coefficients outer witness constant nonnegative
    (center , <ℝ-weaken (normℂ center) outer inside)

  private
    opaque
      derivativesAgree : ∀ n → integratedDerivatives (suc n) ≡ originalDerivatives n
      derivativesAgree n = openInteriorPowerSeriesDerivativeAgrees integrated outer native (suc n) point
        (originalDerivatives n)
        (subst (λ c → HasComplexSum (powerSeriesTermsℂ c center) (originalDerivatives n))
          (sym (repeatedFormalDerivativeℂ-formalPrimitiveℂ n constant coefficients))
          (openInteriorPowerSeriesDerivativeSums coefficients outer witness n point))

      valueAtCenter : integratedDerivatives zero ≡ translatedPrimitiveConstant
      valueAtCenter = openInteriorPowerSeriesDerivativeAgrees integrated outer native zero point translatedPrimitiveConstant
        (closedComplexPowerSeriesPrimitiveHasSum coefficients outer witness constant nonnegative
          (center , <ℝ-weaken (normℂ center) outer inside))

  opaque
    translatedPrimitiveCoefficients :
      complexPowerSeriesTaylorCoefficientsAtCenter integrated outer native center inside ≡
      formalPrimitiveℂ translatedPrimitiveConstant
        (complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside)
    translatedPrimitiveCoefficients = formalPrimitiveℂ-unique translatedPrimitiveConstant
      (taylorCoefficientsℂ originalDerivatives) (taylorCoefficientsℂ integratedDerivatives)
      (taylorCoefficientsℂ-zero integratedDerivatives ∙ valueAtCenter)
      (formalDerivativeℂ-taylorCoefficients integratedDerivatives ∙ cong taylorCoefficientsℂ (funExt derivativesAgree))

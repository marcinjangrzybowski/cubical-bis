module Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Functions.Powers using (powℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (absOfNonnegative)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Density
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Absolute as Real
import Cubical.Analysis.Real.Series.PowerSeries.Majorant as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.InteriorConvergence
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative

opaque
  repeatedDerivativeMajorant-successor : ∀ order coefficients radius →
    complexPowerSeriesMajorant (repeatedFormalDerivativeℂ (suc order) coefficients) radius ≡
      complexPowerSeriesDerivativeMajorant (repeatedFormalDerivativeℂ order coefficients) radius
  repeatedDerivativeMajorant-successor order coefficients radius = funExt λ n →
    cong (_· powℝ radius n)
      (cong₂ _+_ (absMul (realNatural (suc n)) (re (repeatedFormalDerivativeℂ order coefficients (suc n))))
        (absMul (realNatural (suc n)) (im (repeatedFormalDerivativeℂ order coefficients (suc n))))
      ∙ cong (λ x → x · absℝ (re (repeatedFormalDerivativeℂ order coefficients (suc n)))
                    + x · absℝ (im (repeatedFormalDerivativeℂ order coefficients (suc n))))
          (absOfNonnegative (realNatural (suc n)) (realNatural-nonnegative (suc n)))
      ∙ sym (mulDistR (realNatural (suc n))
          (absℝ (re (repeatedFormalDerivativeℂ order coefficients (suc n))))
          (absℝ (im (repeatedFormalDerivativeℂ order coefficients (suc n))))))
    ∙ cong (_· powℝ radius n) (mulComm (realNatural (suc n)) (normℂ (repeatedFormalDerivativeℂ order coefficients (suc n))))
    ∙ sym (mulAssoc (normℂ (repeatedFormalDerivativeℂ order coefficients (suc n))) (realNatural (suc n)) (powℝ radius n))

-- Each induction step uses only one intermediate rational radius and removes
-- its truncation into the proposition of native Cauchy data. This is finite
-- iteration of the interior theorem, not countable selection of tail moduli.
opaque
  repeatedComplexMajorantIsCauchyAtInterior : ∀ order coefficients inner outer →
    0ℝ ≤ℝ inner → inner <ℝ outer →
    Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) →
    Real.IsCauchySeries (complexPowerSeriesMajorant (repeatedFormalDerivativeℂ order coefficients) inner)
  repeatedComplexMajorantIsCauchyAtInterior zero coefficients inner outer positive strict witness =
    Real.dominatedCauchySeriesIsCauchy (complexPowerSeriesMajorant coefficients inner)
      (complexPowerSeriesMajorant coefficients outer)
      (Real.powerSeriesTermAbsBoundByCoefficientMajorant (normℂ ∘ coefficients) (normℂ ∘ coefficients)
        inner outer (Real.nonnegativeCoefficientsSelfMajorized (normℂ ∘ coefficients) (normℂ-nonnegative ∘ coefficients))
        (subst (_≤ℝ outer) (sym (absOfNonnegative inner positive)) (<ℝ-weaken inner outer strict))) witness
  repeatedComplexMajorantIsCauchyAtInterior (suc order) coefficients inner outer positive strict witness =
    PT.rec (Real.isPropIsCauchySeries (complexPowerSeriesMajorant (repeatedFormalDerivativeℂ (suc order) coefficients) inner))
      (λ { (q , below , above) → subst Real.IsCauchySeries (sym (repeatedDerivativeMajorant-successor order coefficients inner))
        (complexPowerSeriesDerivativeMajorantIsCauchyAtInterior (repeatedFormalDerivativeℂ order coefficients)
          inner (rat q) positive below
          (repeatedComplexMajorantIsCauchyAtInterior order coefficients (rat q) outer
            (≤ℝ-trans 0ℝ inner (rat q) positive (<ℝ-weaken inner (rat q) below)) above witness)) })
      (denseℚinℝ inner outer strict)

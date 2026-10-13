module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Approximation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as Nat
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Strict.Base
import Cubical.Analysis.Real.Sequence as Real
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Finite

-- For each fixed coefficient, the translated finite polynomials converge
-- to the canonical Taylor coefficient. Removing the fixed initial delay
-- uses the native sequence shift theorem; it chooses no sequence of tails.
opaque
  finiteTranslatedCoefficientℂLimit : ∀ (coefficients : ComplexSequence) (outer : ℝ)
    (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
    (center : ℂ) (inside : normℂ center <ℝ outer) (order : ℕ) →
    IsComplexLimit (λ count → finiteTranslatedCoefficientsℂ coefficients center count order)
      (complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside order)
  finiteTranslatedCoefficientℂLimit coefficients outer witness center inside order =
    Real.shiftReflectsIsLimitSequence order (re ∘ approximations) (re value) (fst shifted) ,
    Real.shiftReflectsIsLimitSequence order (im ∘ approximations) (im value) (snd shifted)
    where
    approximations : ComplexSequence
    approximations count = finiteTranslatedCoefficientsℂ coefficients center count order

    value : ℂ
    value = complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside order

    shifted : IsComplexLimit (λ count → approximations (order Nat.+ count)) value
    shifted = subst (λ sequence → IsComplexLimit sequence value)
      (funExt λ count → cong (partialSumℂ (translatedCoefficientTermsℂ coefficients center order))
        (sym (Nat.∸+ count order)))
      (translatedCoefficientTermsℂHasSum coefficients outer witness center inside order)

module Cubical.Analysis.Complex.Series.PowerSeries.Translation.RadiusBound where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
import Cubical.Data.Nat.Order as Nat
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Bounds as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Finite
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Majorant

opaque
  finiteTranslatedMajorantBoundOn : ∀ (coefficients : ComplexSequence) (center : ℂ) (radius outer : ℝ) →
    0ℝ ≤ℝ radius → normℂ center + radius ≤ℝ outer → ∀ count →
    Real.partialSum (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius) count
      ≤ℝ Real.partialSum (complexPowerSeriesMajorant coefficients outer) count
  finiteTranslatedMajorantBoundOn coefficients center radius outer positive fits count = ≤ℝ-trans
    (Real.partialSum (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius) count)
    (Real.partialSum (complexPowerSeriesMajorant coefficients (normℂ center + radius)) count)
    (Real.partialSum (complexPowerSeriesMajorant coefficients outer) count)
    (finiteTranslatedMajorantBound coefficients center radius positive count)
    (Real.partialSumMono (complexPowerSeriesMajorant coefficients (normℂ center + radius))
      (complexPowerSeriesMajorant coefficients outer)
      (λ n → mulPres≤L (powℝ (normℂ center + radius) n) (powℝ outer n) (normℂ (coefficients n))
        (0≤→isNonnegative (normℂ (coefficients n)) (normℂ-nonnegative (coefficients n)))
        (powMono {x = normℂ center + radius} {y = outer} n (subst (_≤ℝ normℂ center + radius) (addIdL 0ℝ)
          (addPres≤ 0ℝ (normℂ center) 0ℝ radius (normℂ-nonnegative center) positive)) fits)) count)


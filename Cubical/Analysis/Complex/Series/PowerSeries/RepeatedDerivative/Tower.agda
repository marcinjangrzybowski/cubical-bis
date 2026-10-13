module Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Tower where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Integration.UniformContinuity using (IsRadiuswiseUniformlyContinuous)
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Derivative
open import Cubical.Analysis.Complex.Series.PowerSeries.Derivative.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Convergence
open import Cubical.Analysis.Complex.Calculus.Derivative.Tower
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform

-- One outer witness constructs all values and uniform sums on a smaller
-- bounded coordinate family. Neither derivative values nor a sequence of
-- derivative convergence witnesses is an additional hypothesis.
module _ {ℓ} {A : Type ℓ} (coordinate : A → ℂ) (coefficients : ComplexSequence)
  (inner outer : ℝ) (positive : 0ℝ ≤ℝ inner) (strict : inner <ℝ outer)
  (bounded : ∀ x → normℂ (coordinate x) ≤ℝ inner)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer)) where

  private
    majorantWitness : ∀ order → Real.IsCauchySeries
      (complexPowerSeriesMajorant (repeatedFormalDerivativeℂ order coefficients) inner)
    majorantWitness order = repeatedComplexMajorantIsCauchyAtInterior order coefficients inner outer positive strict witness

  complexHigherDerivativeValue : ℕ → A → ℂ
  complexHigherDerivativeValue order = uniformComplexPowerSeriesValue coordinate
    (repeatedFormalDerivativeℂ order coefficients) inner bounded (majorantWitness order)

  complexHigherDerivativeUniformHasSum : ∀ order →
    UniformHasComplexSum (λ x → powerSeriesTermsℂ (repeatedFormalDerivativeℂ order coefficients) (coordinate x))
      (complexHigherDerivativeValue order)
  complexHigherDerivativeUniformHasSum order = uniformComplexPowerSeriesHasSum coordinate
    (repeatedFormalDerivativeℂ order coefficients) inner bounded (majorantWitness order)

  complexHigherDerivativeHasSum : ∀ order x →
    HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order coefficients) (coordinate x))
      (complexHigherDerivativeValue order x)
  complexHigherDerivativeHasSum order = uniformHasComplexSumAt (complexHigherDerivativeUniformHasSum order)

  complexHigherDerivativeValueAgrees : ∀ order x value →
    HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order coefficients) (coordinate x)) value →
    complexHigherDerivativeValue order x ≡ value
  complexHigherDerivativeValueAgrees order x value = complexSumUnique
    (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order coefficients) (coordinate x))
    (complexHigherDerivativeValue order x) value (complexHigherDerivativeHasSum order x)

  private
    derivativeWitness : ∀ order → Real.IsCauchySeries
      (complexPowerSeriesDerivativeMajorant (repeatedFormalDerivativeℂ order coefficients) inner)
    derivativeWitness order = subst Real.IsCauchySeries (repeatedDerivativeMajorant-successor order coefficients inner)
      (majorantWitness (suc order))

    derivativeSum : ∀ order x →
      HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ (repeatedFormalDerivativeℂ order coefficients)) (coordinate x))
        (complexHigherDerivativeValue (suc order) x)
    derivativeSum order x = subst
      (λ c → HasComplexSum (powerSeriesTermsℂ c (coordinate x)) (complexHigherDerivativeValue (suc order) x))
      (repeatedFormalDerivativeℂ-successor order coefficients) (complexHigherDerivativeHasSum (suc order) x)

  complexPowerSeriesHigherDerivativeTower : ∀ {ℓ'} (source : PremetricStr ℓ' A) →
    isContinuous source coordinate (ℂPremetricSpace .snd) →
    IsComplexDerivativeTowerAlong source coordinate complexHigherDerivativeValue
  complexPowerSeriesHigherDerivativeTower source continuous order = complexPowerSeriesHasFormalDerivativeAlong
    source coordinate (complexHigherDerivativeValue order) (complexHigherDerivativeValue (suc order))
    (repeatedFormalDerivativeℂ order coefficients) inner bounded (derivativeWitness order) continuous
    (complexHigherDerivativeHasSum order) (derivativeSum order)

  complexPowerSeriesHigherUniformDerivative : ∀ {ℓ'} (source : PremetricStr ℓ' A) →
    IsRadiuswiseUniformlyContinuous source coordinate (ℂPremetricSpace .snd) → ∀ order →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate
      (complexHigherDerivativeValue order) (complexHigherDerivativeValue (suc order))
  complexPowerSeriesHigherUniformDerivative source continuous order = complexPowerSeriesHasUniformFormalDerivativeAlong
    source coordinate (complexHigherDerivativeValue order) (complexHigherDerivativeValue (suc order))
    (repeatedFormalDerivativeℂ order coefficients) inner bounded (derivativeWitness order) continuous
    (complexHigherDerivativeHasSum order) (derivativeSum order)

  complexHigherDerivativeIsContinuous : ∀ {ℓ'} (source : PremetricStr ℓ' A) →
    isContinuous source coordinate (ℂPremetricSpace .snd) → ∀ order →
    isContinuous source (complexHigherDerivativeValue order) (ℂPremetricSpace .snd)
  complexHigherDerivativeIsContinuous source continuous order = uniformComplexPowerSeriesIsContinuous source coordinate
    (repeatedFormalDerivativeℂ order coefficients) inner bounded (majorantWitness order) continuous

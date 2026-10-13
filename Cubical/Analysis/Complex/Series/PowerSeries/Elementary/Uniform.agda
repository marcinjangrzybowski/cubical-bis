module Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Exponential.HasSum
open import Cubical.Analysis.Complex.Series.PowerSeries.Trigonometric.HasSum
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base

private
  -- Uniqueness identifies the generic uniformly constructed sum with the
  -- supplied function. No point-indexed selection of convergence data occurs.
  uniformGivenSum : ∀ {ℓ} {A : Type ℓ} (coordinate value : A → ℂ) coefficients radius →
    (∀ x → normℂ (coordinate x) ≤ℝ radius) →
    Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius) →
    (∀ x → HasComplexSum (powerSeriesTermsℂ coefficients (coordinate x)) (value x)) →
    UniformHasComplexSum (λ x → powerSeriesTermsℂ coefficients (coordinate x)) value
  uniformGivenSum coordinate value coefficients radius bounded witness summed =
    subst (UniformHasComplexSum (λ x → powerSeriesTermsℂ coefficients (coordinate x)))
      (funExt λ x → uniformComplexSeriesValueAgrees
        (λ y → powerSeriesTermsℂ coefficients (coordinate y))
        (complexPowerSeriesUniformlyCauchyOn coordinate coefficients radius bounded witness) x (value x , summed x))
      (uniformComplexPowerSeriesHasSum coordinate coefficients radius bounded witness)

exponentialComplexPowerSeriesUniformHasSum : ∀ {ℓ} {A : Type ℓ} (coordinate : A → ℂ) radius →
  0ℝ ≤ℝ radius → (∀ x → normℂ (coordinate x) ≤ℝ radius) →
  UniformHasComplexSum (λ x → powerSeriesTermsℂ exponentialCoefficientsℂ (coordinate x)) (expℂ ∘ coordinate)
exponentialComplexPowerSeriesUniformHasSum coordinate radius positive bounded =
  uniformGivenSum coordinate (expℂ ∘ coordinate) exponentialCoefficientsℂ radius bounded
    (exponentialComplexMajorantIsCauchy radius positive) (exponentialComplexPowerSeriesHasSum ∘ coordinate)

sineComplexPowerSeriesUniformHasSum : ∀ {ℓ} {A : Type ℓ} (coordinate : A → ℂ) radius →
  0ℝ ≤ℝ radius → (∀ x → normℂ (coordinate x) ≤ℝ radius) →
  UniformHasComplexSum (λ x → powerSeriesTermsℂ sineCoefficientsℂ (coordinate x)) (sinℂ ∘ coordinate)
sineComplexPowerSeriesUniformHasSum coordinate radius positive bounded =
  uniformGivenSum coordinate (sinℂ ∘ coordinate) sineCoefficientsℂ radius bounded
    (sineComplexMajorantIsCauchy radius positive) (sineComplexPowerSeriesHasSum ∘ coordinate)

cosineComplexPowerSeriesUniformHasSum : ∀ {ℓ} {A : Type ℓ} (coordinate : A → ℂ) radius →
  0ℝ ≤ℝ radius → (∀ x → normℂ (coordinate x) ≤ℝ radius) →
  UniformHasComplexSum (λ x → powerSeriesTermsℂ cosineCoefficientsℂ (coordinate x)) (cosℂ ∘ coordinate)
cosineComplexPowerSeriesUniformHasSum coordinate radius positive bounded =
  uniformGivenSum coordinate (cosℂ ∘ coordinate) cosineCoefficientsℂ radius bounded
    (cosineComplexMajorantIsCauchy radius positive) (cosineComplexPowerSeriesHasSum ∘ coordinate)

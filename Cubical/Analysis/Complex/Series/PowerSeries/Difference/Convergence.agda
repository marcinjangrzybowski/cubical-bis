module Cubical.Analysis.Complex.Series.PowerSeries.Difference.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Order.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds

powerSeriesDifferenceFactorℂUniformlyCauchy : ∀ {ℓ} {A : Type ℓ}
  coefficients (x y : A → ℂ) radius →
  (∀ p → normℂ (x p) ≤ℝ radius) → (∀ p → normℂ (y p) ≤ℝ radius) →
  Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients radius) →
  UniformlyComplexCauchySeries A (λ p → powerSeriesDifferenceFactorℂ coefficients (x p) (y p))
powerSeriesDifferenceFactorℂUniformlyCauchy coefficients x y radius bx by witness =
  uniformlyDominatedComplexSeriesIsUniformlyCauchy (λ p → powerSeriesDifferenceFactorℂ coefficients (x p) (y p))
    (complexPowerSeriesDerivativeMajorant coefficients radius)
    (λ p → powerSeriesDifferenceFactorℂBound coefficients (x p) (y p) radius (bx p) (by p)) witness

formalDerivativeℂUniformlyCauchy : ∀ {ℓ} {A : Type ℓ} coefficients (coordinate : A → ℂ) radius →
  (∀ x → normℂ (coordinate x) ≤ℝ radius) →
  Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients radius) →
  UniformlyComplexCauchySeries A (λ x → powerSeriesTermsℂ (formalDerivativeℂ coefficients) (coordinate x))
formalDerivativeℂUniformlyCauchy coefficients coordinate radius bounded witness =
  uniformlyDominatedComplexSeriesIsUniformlyCauchy (λ x → powerSeriesTermsℂ (formalDerivativeℂ coefficients) (coordinate x))
    (complexPowerSeriesDerivativeMajorant coefficients radius)
    (λ x → formalDerivativeℂTermBound coefficients (coordinate x) radius (bounded x)) witness

formalDerivativeℂValue : ∀ {ℓ} {A : Type ℓ} coefficients (coordinate : A → ℂ) radius →
  (∀ x → normℂ (coordinate x) ≤ℝ radius) →
  Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients radius) → A → ℂ
formalDerivativeℂValue coefficients coordinate radius bounded witness =
  uniformComplexSeriesValue (λ x → powerSeriesTermsℂ (formalDerivativeℂ coefficients) (coordinate x))
    (formalDerivativeℂUniformlyCauchy coefficients coordinate radius bounded witness)

formalDerivativeℂValueHasSum : ∀ {ℓ} {A : Type ℓ} coefficients (coordinate : A → ℂ) radius
  (bounded : ∀ x → normℂ (coordinate x) ≤ℝ radius)
  (witness : Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients radius)) → ∀ x →
  HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (coordinate x))
    (formalDerivativeℂValue coefficients coordinate radius bounded witness x)
formalDerivativeℂValueHasSum coefficients coordinate radius bounded witness =
  uniformHasComplexSumAt (uniformlyComplexCauchySeriesHasUniformSum
    (λ x → powerSeriesTermsℂ (formalDerivativeℂ coefficients) (coordinate x))
    (formalDerivativeℂUniformlyCauchy coefficients coordinate radius bounded witness))

formalDerivativeℂValueIsContinuous : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
  coefficients (coordinate : A → ℂ) radius (bounded : ∀ x → normℂ (coordinate x) ≤ℝ radius)
  (witness : Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients radius)) →
  isContinuous source coordinate (ℂPremetricSpace .snd) →
  isContinuous source (formalDerivativeℂValue coefficients coordinate radius bounded witness) (ℂPremetricSpace .snd)
formalDerivativeℂValueIsContinuous source coefficients coordinate radius bounded witness continuous =
  uniformComplexSeriesValueIsContinuous source
    (λ x → powerSeriesTermsℂ (formalDerivativeℂ coefficients) (coordinate x))
    (formalDerivativeℂUniformlyCauchy coefficients coordinate radius bounded witness)
    (powerSeriesTermℂIsContinuous source coordinate (formalDerivativeℂ coefficients) continuous)

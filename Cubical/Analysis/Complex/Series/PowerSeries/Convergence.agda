module Cubical.Analysis.Complex.Series.PowerSeries.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Order.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Absolute
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds

-- One native Cauchy witness for a radius majorant constructs values at
-- every point of the closed l1 ball. No point-indexed choices are made.
complexPowerSeriesAbsolutelyCauchyOn : ∀ coefficients radius →
  Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius) →
  ∀ z → normℂ z ≤ℝ radius → IsComplexAbsolutelyCauchySeries (powerSeriesTermsℂ coefficients z)
complexPowerSeriesAbsolutelyCauchyOn coefficients radius witness z bounded =
  dominatedComplexSeriesIsAbsolutelyCauchy (powerSeriesTermsℂ coefficients z)
    (complexPowerSeriesMajorant coefficients radius) (complexPowerSeriesTermBound coefficients z radius bounded) witness

complexPowerSeriesIsCauchyOn : ∀ coefficients radius →
  Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius) →
  ∀ z → normℂ z ≤ℝ radius → IsComplexCauchySeries (powerSeriesTermsℂ coefficients z)
complexPowerSeriesIsCauchyOn coefficients radius witness z bounded =
  dominatedComplexSeriesIsCauchy (powerSeriesTermsℂ coefficients z)
    (complexPowerSeriesMajorant coefficients radius) (complexPowerSeriesTermBound coefficients z radius bounded) witness

complexPowerSeriesSummableOn : ∀ coefficients radius →
  Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius) →
  ∀ z → normℂ z ≤ℝ radius → ComplexPowerSeriesSummableAt coefficients z
complexPowerSeriesSummableOn coefficients radius witness z bounded =
  complexCauchySeriesIsSummable (powerSeriesTermsℂ coefficients z)
    (complexPowerSeriesIsCauchyOn coefficients radius witness z bounded)

complexPowerSeriesUniformlyCauchyOn : ∀ {ℓ} {A : Type ℓ} (coordinate : A → ℂ) coefficients radius →
  (∀ x → normℂ (coordinate x) ≤ℝ radius) → Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius) →
  UniformlyComplexCauchySeries A (λ x → powerSeriesTermsℂ coefficients (coordinate x))
complexPowerSeriesUniformlyCauchyOn coordinate coefficients radius bounded witness =
  uniformlyDominatedComplexSeriesIsUniformlyCauchy (λ x → powerSeriesTermsℂ coefficients (coordinate x))
    (complexPowerSeriesMajorant coefficients radius)
    (λ x → complexPowerSeriesTermBound coefficients (coordinate x) radius (bounded x)) witness

-- The value agrees with every supplied pointwise sum by the generic
-- uniformComplexSeriesValueAgrees theorem.
uniformComplexPowerSeriesValue : ∀ {ℓ} {A : Type ℓ} (coordinate : A → ℂ) coefficients radius →
  (∀ x → normℂ (coordinate x) ≤ℝ radius) → Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius) → A → ℂ
uniformComplexPowerSeriesValue coordinate coefficients radius bounded witness = uniformComplexSeriesValue
  (λ x → powerSeriesTermsℂ coefficients (coordinate x))
  (complexPowerSeriesUniformlyCauchyOn coordinate coefficients radius bounded witness)

uniformComplexPowerSeriesHasSum : ∀ {ℓ} {A : Type ℓ} (coordinate : A → ℂ) coefficients radius
  (bounded : ∀ x → normℂ (coordinate x) ≤ℝ radius) (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius)) →
  UniformHasComplexSum (λ x → powerSeriesTermsℂ coefficients (coordinate x))
    (uniformComplexPowerSeriesValue coordinate coefficients radius bounded witness)
uniformComplexPowerSeriesHasSum coordinate coefficients radius bounded witness =
  uniformlyComplexCauchySeriesHasUniformSum (λ x → powerSeriesTermsℂ coefficients (coordinate x))
    (complexPowerSeriesUniformlyCauchyOn coordinate coefficients radius bounded witness)

uniformComplexPowerSeriesIsContinuous : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
  (coordinate : A → ℂ) coefficients radius (bounded : ∀ x → normℂ (coordinate x) ≤ℝ radius)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius)) →
  isContinuous source coordinate (ℂPremetricSpace .snd) →
  isContinuous source (uniformComplexPowerSeriesValue coordinate coefficients radius bounded witness) (ℂPremetricSpace .snd)
uniformComplexPowerSeriesIsContinuous source coordinate coefficients radius bounded witness continuous =
  uniformComplexSeriesValueIsContinuous source (λ x → powerSeriesTermsℂ coefficients (coordinate x))
    (complexPowerSeriesUniformlyCauchyOn coordinate coefficients radius bounded witness)
    (powerSeriesTermℂIsContinuous source coordinate coefficients continuous)

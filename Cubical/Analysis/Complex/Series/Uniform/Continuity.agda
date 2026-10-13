module Cubical.Analysis.Complex.Series.Uniform.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Integration.UniformContinuity
import Cubical.Analysis.Real.Series.PowerSeries.Difference.UniformDerivative.Factors as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Continuity.Uniform
open import Cubical.Analysis.Complex.Series.Uniform

-- Reuse the real uniform-tail/finite-sum theorem for both coordinates.
-- Each requested tolerance uses only finitely many truncated witnesses.
uniformComplexSeriesValueIsRadiuswiseUniformlyContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (terms : A → ComplexSequence)
  (uniform : UniformlyComplexCauchySeries A terms) →
  (∀ n → IsRadiuswiseUniformlyContinuous source (λ x → terms x n) (ℂPremetricSpace .snd)) →
  IsRadiuswiseUniformlyContinuous source (uniformComplexSeriesValue terms uniform) (ℂPremetricSpace .snd)
uniformComplexSeriesValueIsRadiuswiseUniformlyContinuous source terms uniform continuous =
  pairComplexUniform source _ _
    (Real.uniformSeriesValueIsRadiuswiseUniformlyContinuous source (λ x → re ∘ terms x) (fst uniform)
      (λ n → reComplexUniform source (λ x → terms x n) (continuous n)))
    (Real.uniformSeriesValueIsRadiuswiseUniformlyContinuous source (λ x → im ∘ terms x) (snd uniform)
      (λ n → imComplexUniform source (λ x → terms x n) (continuous n)))

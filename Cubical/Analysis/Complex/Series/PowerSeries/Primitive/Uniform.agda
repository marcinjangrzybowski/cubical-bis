module Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Integration.UniformContinuity
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.AtZero
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Derivative.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Convergence
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform

module _ {ℓ} {A : Type ℓ} (coordinate : A → ℂ) (constant : ℂ)
  (coefficients : ComplexSequence) (radius : ℝ) (nonnegative : 0ℝ ≤ℝ radius)
  (bounded : ∀ x → normℂ (coordinate x) ≤ℝ radius)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius)) where
  private
    integrated : ComplexSequence
    integrated = formalPrimitiveℂ constant coefficients
    native : Real.IsCauchySeries (complexPowerSeriesMajorant integrated radius)
    native = formalPrimitiveℂMajorantIsCauchy constant coefficients radius nonnegative witness

  -- Keep the completed value abstract; sum laws are the comparison API.
  opaque
    uniformComplexPowerSeriesPrimitive : A → ℂ
    uniformComplexPowerSeriesPrimitive = uniformComplexPowerSeriesValue coordinate integrated radius bounded native

    uniformComplexPowerSeriesPrimitiveHasUniformSum : UniformHasComplexSum
      (λ x → powerSeriesTermsℂ integrated (coordinate x)) uniformComplexPowerSeriesPrimitive
    uniformComplexPowerSeriesPrimitiveHasUniformSum = uniformComplexPowerSeriesHasSum coordinate integrated radius bounded native

  uniformComplexPowerSeriesPrimitiveHasSum : ∀ x →
    HasComplexSum (powerSeriesTermsℂ integrated (coordinate x)) (uniformComplexPowerSeriesPrimitive x)
  uniformComplexPowerSeriesPrimitiveHasSum = uniformHasComplexSumAt uniformComplexPowerSeriesPrimitiveHasUniformSum

  uniformComplexPowerSeriesPrimitiveAgrees : ∀ x value →
    HasComplexSum (powerSeriesTermsℂ integrated (coordinate x)) value → uniformComplexPowerSeriesPrimitive x ≡ value
  uniformComplexPowerSeriesPrimitiveAgrees x value = complexSumUnique
    (powerSeriesTermsℂ integrated (coordinate x)) (uniformComplexPowerSeriesPrimitive x) value
    (uniformComplexPowerSeriesPrimitiveHasSum x)

  uniformComplexPowerSeriesPrimitiveAtZero : ∀ x → coordinate x ≡ 0ℂ → uniformComplexPowerSeriesPrimitive x ≡ constant
  uniformComplexPowerSeriesPrimitiveAtZero x atZero = complexPowerSeriesValueAtZero integrated
    (uniformComplexPowerSeriesPrimitive x)
    (subst (λ z → HasComplexSum (powerSeriesTermsℂ integrated z) (uniformComplexPowerSeriesPrimitive x))
      atZero (uniformComplexPowerSeriesPrimitiveHasSum x))

  opaque
    uniformComplexPowerSeriesPrimitiveHasDerivativeAlong : ∀ {ℓ'} (source : PremetricStr ℓ' A) →
      IsRadiuswiseUniformlyContinuous source coordinate (ℂPremetricSpace .snd) →
      IsRadiuswiseUniformComplexDerivativeAlong source coordinate uniformComplexPowerSeriesPrimitive
        (uniformComplexPowerSeriesValue coordinate coefficients radius bounded witness)
    uniformComplexPowerSeriesPrimitiveHasDerivativeAlong source continuous =
      complexPowerSeriesHasUniformFormalDerivativeAlong source coordinate uniformComplexPowerSeriesPrimitive
        (uniformComplexPowerSeriesValue coordinate coefficients radius bounded witness) integrated radius bounded
        (formalPrimitiveℂDerivativeMajorantIsCauchy constant coefficients radius witness) continuous
        uniformComplexPowerSeriesPrimitiveHasSum
        (λ x → subst (λ c → HasComplexSum (powerSeriesTermsℂ c (coordinate x))
          (uniformComplexPowerSeriesValue coordinate coefficients radius bounded witness x))
          (sym (formalDerivativeℂ-formalPrimitiveℂ constant coefficients))
          (uniformHasComplexSumAt (uniformComplexPowerSeriesHasSum coordinate coefficients radius bounded witness) x))

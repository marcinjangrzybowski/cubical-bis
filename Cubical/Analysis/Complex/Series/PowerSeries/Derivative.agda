module Cubical.Analysis.Complex.Series.PowerSeries.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Order.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Continuity
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Continuity
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Sum
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Convergence
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Factor

-- The sums may be supplied independently of native convergence data. Only
-- the derivative majorant needs a native Cauchy witness to construct the
-- continuous divided difference. This is complex-linear differentiation
-- along the coordinate, not differentiation along the real axis alone.
opaque
  complexPowerSeriesHasFormalDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate f d : A → ℂ) coefficients radius →
    (∀ x → normℂ (coordinate x) ≤ℝ radius) →
    Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients radius) →
    isContinuous source coordinate (ℂPremetricSpace .snd) →
    (∀ x → HasComplexSum (powerSeriesTermsℂ coefficients (coordinate x)) (f x)) →
    (∀ x → HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (coordinate x)) (d x)) →
    IsComplexDerivativeAlong source coordinate f d
  complexPowerSeriesHasFormalDerivativeAlong {A = A} source coordinate f d coefficients radius bounded witness continuous fs ds x =
    continuousComplexDifferenceFactorGivesDerivativeAt source coordinate f (d x) x factor
      (λ y → powerSeriesValueℂDifferenceFactorization coefficients (coordinate x) (coordinate y)
        (f x) (f y) (factor y) (fs x) (fs y) (factorSum y))
      (powerSeriesDifferenceFactorℂDiagonalValue coefficients (coordinate x) (factor x) (d x) (factorSum x) (ds x))
      (uniformComplexSeriesValueIsContinuous source terms uniform
        (powerSeriesDifferenceFactorℂIsContinuous source coefficients (λ _ → coordinate x) coordinate
          (constantℂ-isContinuous source (coordinate x)) continuous) x)
    where
    terms : A → ComplexSequence
    terms y = powerSeriesDifferenceFactorℂ coefficients (coordinate x) (coordinate y)

    uniform : UniformlyComplexCauchySeries A terms
    uniform = powerSeriesDifferenceFactorℂUniformlyCauchy coefficients (λ _ → coordinate x) coordinate radius
      (λ _ → bounded x) bounded witness

    factor : A → ℂ
    factor = uniformComplexSeriesValue terms uniform

    factorSum : ∀ y → HasComplexSum (terms y) (factor y)
    factorSum = uniformHasComplexSumAt (uniformlyComplexCauchySeriesHasUniformSum terms uniform)

-- Canonical sums from two supplied real majorants. Continuity of the
-- derivative is separately available as formalDerivativeℂValueIsContinuous.
uniformComplexPowerSeriesHasFormalDerivative : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (coordinate : A → ℂ) coefficients radius
  (bounded : ∀ x → normℂ (coordinate x) ≤ℝ radius)
  (original : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius))
  (derivative : Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients radius)) →
  isContinuous source coordinate (ℂPremetricSpace .snd) →
  IsComplexDerivativeAlong source coordinate
    (uniformComplexPowerSeriesValue coordinate coefficients radius bounded original)
    (formalDerivativeℂValue coefficients coordinate radius bounded derivative)
uniformComplexPowerSeriesHasFormalDerivative source coordinate coefficients radius bounded original derivative continuous =
  complexPowerSeriesHasFormalDerivativeAlong source coordinate
    (uniformComplexPowerSeriesValue coordinate coefficients radius bounded original)
    (formalDerivativeℂValue coefficients coordinate radius bounded derivative)
    coefficients radius bounded derivative continuous
    (uniformHasComplexSumAt (uniformComplexPowerSeriesHasSum coordinate coefficients radius bounded original))
    (formalDerivativeℂValueHasSum coefficients coordinate radius bounded derivative)

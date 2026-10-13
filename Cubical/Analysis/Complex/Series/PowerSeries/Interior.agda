module Cubical.Analysis.Complex.Series.PowerSeries.Interior where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Density
open import Cubical.Analysis.Real.Integration.UniformContinuity using (IsRadiuswiseUniformlyContinuous)
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Derivative
open import Cubical.Analysis.Complex.Series.PowerSeries.Derivative.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.InteriorConvergence
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Calculus.Derivative.OpenSubspace

complexPowerSeriesHasFormalDerivativeFromOuterRadius : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (coordinate f d : A → ℂ) coefficients inner outer →
  0ℝ ≤ℝ inner → inner <ℝ outer → (∀ x → normℂ (coordinate x) ≤ℝ inner) →
  Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) →
  isContinuous source coordinate (ℂPremetricSpace .snd) →
  (∀ x → HasComplexSum (powerSeriesTermsℂ coefficients (coordinate x)) (f x)) →
  (∀ x → HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (coordinate x)) (d x)) →
  IsComplexDerivativeAlong source coordinate f d
complexPowerSeriesHasFormalDerivativeFromOuterRadius source coordinate f d coefficients inner outer positive strict bounded witness =
  complexPowerSeriesHasFormalDerivativeAlong source coordinate f d coefficients inner bounded
    (complexPowerSeriesDerivativeMajorantIsCauchyAtInterior coefficients inner outer positive strict witness)

complexPowerSeriesHasUniformFormalDerivativeFromOuterRadius : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (coordinate f d : A → ℂ) coefficients inner outer →
  0ℝ ≤ℝ inner → inner <ℝ outer → (∀ x → normℂ (coordinate x) ≤ℝ inner) →
  Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) →
  IsRadiuswiseUniformlyContinuous source coordinate (ℂPremetricSpace .snd) →
  (∀ x → HasComplexSum (powerSeriesTermsℂ coefficients (coordinate x)) (f x)) →
  (∀ x → HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (coordinate x)) (d x)) →
  IsRadiuswiseUniformComplexDerivativeAlong source coordinate f d
complexPowerSeriesHasUniformFormalDerivativeFromOuterRadius source coordinate f d coefficients inner outer positive strict bounded witness =
  complexPowerSeriesHasUniformFormalDerivativeAlong source coordinate f d coefficients inner bounded
    (complexPowerSeriesDerivativeMajorantIsCauchyAtInterior coefficients inner outer positive strict witness)

-- This conclusion is an ambient complex derivative, with no derivative
-- convergence hypothesis. The two ambient functions need only represent
-- the respective sums on the open outer radius. A rational intermediate
-- radius exists under truncation, which is eliminated into differentiability.
opaque
  complexPowerSeriesHasFormalDerivativeAtInterior : ∀ coefficients outer (function derivative : ℂ → ℂ) →
    Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) →
    (∀ z → normℂ z <ℝ outer → HasComplexSum (powerSeriesTermsℂ coefficients z) (function z)) →
    (∀ z → normℂ z <ℝ outer → HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) z) (derivative z)) →
    ∀ z → normℂ z <ℝ outer → IsComplexDerivativeAt function (derivative z) z
  complexPowerSeriesHasFormalDerivativeAtInterior coefficients outer function derivative witness fs ds z inside =
    PT.rec (isPropIsComplexDerivativeAlongAt (ℂPremetricSpace .snd) (idfun ℂ) function (derivative z) z)
      (λ { (q , below , above) → atRadius (rat q) below above }) (denseℚinℝ (normℂ z) outer inside)
    where
    atRadius : ∀ inner → normℂ z <ℝ inner → inner <ℝ outer → IsComplexDerivativeAt function (derivative z) z
    atRadius inner below above = openSubspaceComplexDerivativeAt
      (OpenComplexNormRadiusPredicate inner) (openComplexNormRadiusIsOpen inner) function derivative
      (complexPowerSeriesHasFormalDerivativeFromOuterRadius
        (OpenComplexNormRadiusPremetricSpace inner .snd) fst (function ∘ fst) (derivative ∘ fst)
        coefficients inner outer
        (≤ℝ-trans 0ℝ (normℂ z) inner (normℂ-nonnegative z) (<ℝ-weaken (normℂ z) inner below)) above
        (λ point → <ℝ-weaken (normℂ (fst point)) inner (snd point)) witness
        (snd (NE→C (openComplexNormRadiusInclusionNE inner)))
        (λ point → fs (fst point) (<ℝ-trans (normℂ (fst point)) inner outer (snd point) above))
        (λ point → ds (fst point) (<ℝ-trans (normℂ (fst point)) inner outer (snd point) above))) z below

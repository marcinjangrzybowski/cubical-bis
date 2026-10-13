module Cubical.Analysis.Complex.Series.PowerSeries.Difference.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Continuity.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds
import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Algebra as Algebra

opaque
  boundedPowerComplexUniform : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (coordinate : A → ℂ) radius → (∀ x → normℂ (coordinate x) ≤ℝ radius) →
    IsRadiuswiseUniformlyContinuous source coordinate (ℂPremetricSpace .snd) → ∀ n →
    IsRadiuswiseUniformlyContinuous source (λ x → coordinate x ^ℂ n) (ℂPremetricSpace .snd)
  boundedPowerComplexUniform source coordinate radius bounded continuous =
    Algebra.DifferenceAlgebra.powerInduction ℂCommRing
      (λ f → IsRadiuswiseUniformlyContinuous source f (ℂPremetricSpace .snd)) coordinate
      (constantComplexUniform source 1ℂ)
      (λ n previous → boundedProductComplexUniform source coordinate (λ x → coordinate x ^ℂ n) radius (powℝ radius n)
        bounded (λ x → complexPowerNormBoundOn (coordinate x) radius (bounded x) n) continuous previous)

opaque
  powerDifferenceFactorℂUniform : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (x y : A → ℂ) radius → (∀ p → normℂ (x p) ≤ℝ radius) → (∀ p → normℂ (y p) ≤ℝ radius) →
    IsRadiuswiseUniformlyContinuous source x (ℂPremetricSpace .snd) →
    IsRadiuswiseUniformlyContinuous source y (ℂPremetricSpace .snd) → ∀ n →
    IsRadiuswiseUniformlyContinuous source (λ p → powerDifferenceFactorℂ (x p) (y p) n) (ℂPremetricSpace .snd)
  powerDifferenceFactorℂUniform source x y radius bx by ux uy zero =
    subst (λ f → IsRadiuswiseUniformlyContinuous source f (ℂPremetricSpace .snd))
      (sym (funExt (λ p → powerDifferenceFactorℂ-zero (x p) (y p)))) (constantComplexUniform source 1ℂ)
  powerDifferenceFactorℂUniform source x y radius bx by ux uy (suc n) =
    subst (λ f → IsRadiuswiseUniformlyContinuous source f (ℂPremetricSpace .snd))
      (sym (funExt (λ p → powerDifferenceFactorℂ-step (x p) (y p) n)))
      (sumComplexUniform source (λ p → y p ^ℂ suc n) (λ p → x p ·ℂ powerDifferenceFactorℂ (x p) (y p) n)
        (boundedPowerComplexUniform source y radius by uy (suc n))
        (boundedProductComplexUniform source x (λ p → powerDifferenceFactorℂ (x p) (y p) n)
          radius (realNatural (suc n) · powℝ radius n) bx
          (λ p → powerDifferenceFactorℂBound (x p) (y p) radius (bx p) (by p) n) ux
          (powerDifferenceFactorℂUniform source x y radius bx by ux uy n)))

powerSeriesDifferenceFactorℂUniform : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
  coefficients (x y : A → ℂ) radius →
  (∀ p → normℂ (x p) ≤ℝ radius) → (∀ p → normℂ (y p) ≤ℝ radius) →
  IsRadiuswiseUniformlyContinuous source x (ℂPremetricSpace .snd) →
  IsRadiuswiseUniformlyContinuous source y (ℂPremetricSpace .snd) → ∀ n →
  IsRadiuswiseUniformlyContinuous source (λ p → powerSeriesDifferenceFactorℂ coefficients (x p) (y p) n) (ℂPremetricSpace .snd)
powerSeriesDifferenceFactorℂUniform source coefficients x y radius bx by ux uy n =
  boundedProductComplexUniform source (λ _ → coefficients (suc n)) (λ p → powerDifferenceFactorℂ (x p) (y p) n)
    (normℂ (coefficients (suc n))) (realNatural (suc n) · powℝ radius n)
    (λ _ → ≤ℝ-refl (normℂ (coefficients (suc n))))
    (λ p → powerDifferenceFactorℂBound (x p) (y p) radius (bx p) (by p) n)
    (constantComplexUniform source (coefficients (suc n)))
    (powerDifferenceFactorℂUniform source x y radius bx by ux uy n)

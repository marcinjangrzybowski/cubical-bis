module Cubical.Analysis.Complex.Calculus.Derivative.Translation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (suc)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Tower

-- Translating the coordinate does not change its increments or derivatives.
-- This applies also to intrinsic functions on open subspaces.
opaque
  untranslateComplexDerivativeCoordinateAlongAt : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate function : A → ℂ) center value x →
    IsComplexDerivativeAlongAt source (λ y → center +ℂ coordinate y) function value x →
    IsComplexDerivativeAlongAt source coordinate function value x
  untranslateComplexDerivativeCoordinateAlongAt source coordinate function center value x differentiable ε =
    PT.map (λ { (δ , estimate) → δ , λ y close →
      subst (λ displacement → normℂ ((function y -ℂ function x) -ℂ value ·ℂ displacement)
        ≤ℝ rat (fst ε) · normℂ displacement)
        (sym (ℂRing.translatedDifference center (coordinate y) (coordinate x))) (estimate y close) }) (differentiable ε)

translateComplexDerivativeTower : ∀ derivatives → IsComplexDerivativeTower derivatives → ∀ center →
  IsComplexDerivativeTower (λ n z → derivatives n (center +ℂ z))
translateComplexDerivativeTower derivatives tower center n z = untranslateComplexDerivativeCoordinateAlongAt
  (ℂPremetricSpace .snd) (idfun ℂ) (λ w → derivatives n (center +ℂ w)) center
  (derivatives (suc n) (center +ℂ z)) z
  (pullbackComplexDerivativeAlong (ℂPremetricSpace .snd) (ℂPremetricSpace .snd) (idfun ℂ)
    (derivatives n) (derivatives (suc n)) (center +ℂ_) (snd (NE→C translationNE)) (tower n) z)
  where
  translationNE : NE[ ℂPremetricSpace , ℂPremetricSpace ]
  fst translationNE = center +ℂ_
  IsNonExpanding.pres≈ (snd translationNE) = addℂ-presClosenessL center

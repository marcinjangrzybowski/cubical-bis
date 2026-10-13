module Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Translation where

open import Cubical.Foundations.Prelude
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
import Cubical.Analysis.Complex.Algebra.Identities as Identities

private module C = Identities.Identities ℂCommRing

-- Translation changes neither differences of values nor differences of
-- coordinates. The same truncated radius works at every error tolerance.
opaque
  translateUniformComplexDerivativeValues : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate function derivative : A → ℂ) offset →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate function derivative →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate (λ x → function x +ℂ offset) derivative
  translateUniformComplexDerivativeValues source coordinate function derivative offset uniform ε =
    PT.map (λ { (δ , near) → δ , λ x y close →
      subst (λ difference → normℂ (difference -ℂ derivative x ·ℂ (coordinate y -ℂ coordinate x))
        ≤ℝ rat (fst ε) · normℂ (coordinate y -ℂ coordinate x))
        (ℂRing.translatedDifference offset (function y) (function x)
          ∙ cong₂ _-ℂ_ (+ℂComm offset (function y)) (+ℂComm offset (function x)))
        (near x y close) }) (uniform ε)

  unshiftUniformComplexDerivativeCoordinate : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate function derivative : A → ℂ) center →
    IsRadiuswiseUniformComplexDerivativeAlong source (λ x → coordinate x -ℂ center) function derivative →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate function derivative
  unshiftUniformComplexDerivativeCoordinate source coordinate function derivative center uniform ε =
    PT.map (λ { (δ , near) → δ , λ x y close →
      subst (λ displacement → normℂ ((function y -ℂ function x) -ℂ derivative x ·ℂ displacement)
        ≤ℝ rat (fst ε) · normℂ displacement)
        (C.subtractSameRight (coordinate y) (coordinate x) center) (near x y close) }) (uniform ε)

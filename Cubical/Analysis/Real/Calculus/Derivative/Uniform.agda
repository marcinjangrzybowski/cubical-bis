module Cubical.Analysis.Real.Calculus.Derivative.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Base


-- A radius is eliminated independently at each requested error.  This does
-- not select a modulus, and the domain may be a closed interval or radius.
IsRadiuswiseUniformDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ} → PremetricStr ℓ' A →
  (coordinate function derivative : A → ℝ) → Type (ℓ-max ℓ ℓ')
IsRadiuswiseUniformDerivativeAlong source coordinate function derivative =
  ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
    (∀ x y → PremetricStr._≈[_]_ source x δ y →
      absℝ (derivativeErrorAlong coordinate function derivative x y)
        ≤ℝ rat (fst ε) · absℝ (coordinate y - coordinate x))


uniformDerivativeAlong→derivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ) →
  IsRadiuswiseUniformDerivativeAlong source coordinate function derivative →
  IsDerivativeAlong source coordinate function derivative
uniformDerivativeAlong→derivativeAlong source coordinate function derivative
    uniform x ε = PT.map (λ { (δ , bound) → δ , bound x }) (uniform ε)

module Cubical.Analysis.Real.Integration.UniformContinuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base


-- Integral estimates only need one input radius at a time. Keeping that
-- radius truncated avoids adding a choice principle for a global modulus.
-- The general existence theorem in RiemannIntegral.UniformContinuity uses
-- the standard isUniformlyContinuous predicate to construct a sequence limit.
IsRadiuswiseUniformlyContinuous :
  ∀ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {B : Type ℓB} →
  PremetricStr ℓA' A → (A → B) → PremetricStr ℓB' B →
  Type (ℓ-max (ℓ-max ℓA ℓA') ℓB')
IsRadiuswiseUniformlyContinuous source f target =
  ∀ ε →
    ∃[ δ ∈ ℚ₊ ]
      (∀ x y →
        PremetricStr._≈[_]_ source x δ y →
        PremetricStr._≈[_]_ target (f x) ε (f y))


isPropIsRadiuswiseUniformlyContinuous :
  ∀ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {B : Type ℓB}
  (source : PremetricStr ℓA' A) (f : A → B)
  (target : PremetricStr ℓB' B) →
  isProp (IsRadiuswiseUniformlyContinuous source f target)
isPropIsRadiuswiseUniformlyContinuous source f target =
  isPropΠ λ _ → squash₁


isUniformlyContinuous→isRadiuswiseUniformlyContinuous :
  ∀ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {B : Type ℓB}
  (source : PremetricStr ℓA' A) (f : A → B)
  (target : PremetricStr ℓB' B) →
  isUniformlyContinuous source f target →
  IsRadiuswiseUniformlyContinuous source f target
isUniformlyContinuous→isRadiuswiseUniformlyContinuous
  source f target f-uc ε =
  PT.map
    (λ { (μ , uc) →
      μ ε , λ x y →
        IsUniformlyContinuousWith.pres≈ uc x y ε })
    f-uc


radiuswisePrecomposeNonExpanding :
  ∀ {ℓA ℓA' ℓB ℓB' ℓC ℓC'}
  {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
  (source : PremetricStr ℓA' A)
  (middle : PremetricStr ℓB' B)
  (target : PremetricStr ℓC' C)
  (g : A → B) (f : B → C) →
  IsNonExpanding source g middle →
  IsRadiuswiseUniformlyContinuous middle f target →
  IsRadiuswiseUniformlyContinuous source (f ∘ g) target
radiuswisePrecomposeNonExpanding
  source middle target g f g-ne f-uc ε =
  PT.map
    (λ { (δ , close) →
      δ , λ x y x≈y →
        close (g x) (g y)
          (IsNonExpanding.pres≈ g-ne x y δ x≈y) })
    (f-uc ε)


IsRadiuswiseUniformlyContinuousℝ : (ℝ → ℝ) → Type₀
IsRadiuswiseUniformlyContinuousℝ f =
  IsRadiuswiseUniformlyContinuous
    (snd ℝPremetricSpace) f (snd ℝPremetricSpace)


isUniformlyContinuousℝ→isRadiuswiseUniformlyContinuousℝ : ∀ f →
  isUniformlyContinuous
    (snd ℝPremetricSpace) f (snd ℝPremetricSpace) →
  IsRadiuswiseUniformlyContinuousℝ f
isUniformlyContinuousℝ→isRadiuswiseUniformlyContinuousℝ f =
  isUniformlyContinuous→isRadiuswiseUniformlyContinuous
    (snd ℝPremetricSpace) f (snd ℝPremetricSpace)

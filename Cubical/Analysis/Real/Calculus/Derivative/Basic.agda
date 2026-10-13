module Cubical.Analysis.Real.Calculus.Derivative.Basic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Slack
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

opaque
  constantHasUniformDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate : A → ℝ) (constant : ℝ) →
    IsRadiuswiseUniformDerivativeAlong source coordinate (λ _ → constant) (λ _ → 0ℝ)
  constantHasUniformDerivativeAlong source coordinate constant ε = return
    (ε , λ x y _ →
      subst (λ error → absℝ error ≤ℝ rat (fst ε) · absℝ (coordinate y - coordinate x))
        (sym (cong₂ _-_ (subSelf constant) (ℝRing.0LeftAnnihilates (coordinate y - coordinate x)) ∙ subSelf 0ℝ))
        (subst (_≤ℝ rat (fst ε) · absℝ (coordinate y - coordinate x))
          (ℝRing.0LeftAnnihilates (absℝ (coordinate y - coordinate x)) ∙ sym absZero)
          (mulPres≤R-0≤ 0ℝ (rat (fst ε)) (absℝ (coordinate y - coordinate x))
            (absNonnegative (coordinate y - coordinate x)) (<ℝ-weaken 0ℝ (rat (fst ε)) (positiveSlack ε)))))


constantHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ)
    (constant : ℝ) →
  IsDerivativeAlong
    source coordinate
    (λ _ → constant)
    (λ _ → 0ℝ)
constantHasDerivativeAlong source coordinate constant =
  continuousDifferenceFactorGivesDerivative
    source coordinate
    (λ _ → constant)
    (λ _ → 0ℝ)
    (λ _ → 0ℝ)
    (λ x y →
      subSelf constant
      ∙ sym
        (ℝRing.0RightAnnihilates
          (coordinate y - coordinate x)))
    (λ _ → refl)
    constant-factor-continuous
  where
  constant-factor-continuous :
    isContinuous
      (PremetricProductStr source source)
      (λ _ → 0ℝ)
      (ℝPremetricSpace .snd)
  constant-factor-continuous point
    .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ _ → refl∼ 0ℝ ε
      )


coordinateHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ) →
  IsDerivativeAlong
    source coordinate
    coordinate
    (λ _ → 1ℝ)
coordinateHasDerivativeAlong source coordinate =
  continuousDifferenceFactorGivesDerivative
    source coordinate coordinate
    (λ _ → 1ℝ)
    (λ _ → 1ℝ)
    (λ x y →
      sym
        (mulIdR
          (coordinate y - coordinate x)))
    (λ _ → refl)
    constant-factor-continuous
  where
  constant-factor-continuous :
    isContinuous
      (PremetricProductStr source source)
      (λ _ → 1ℝ)
      (ℝPremetricSpace .snd)
  constant-factor-continuous point
    .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ _ → refl∼ 1ℝ ε
      )


constantHasDerivative : ∀ constant →
  IsDerivative
    (λ _ → constant)
    (λ _ → 0ℝ)
constantHasDerivative constant =
  constantHasDerivativeAlong
    (ℝPremetricSpace .snd)
    (idfun ℝ) constant


identityHasDerivative :
  IsDerivative
    (idfun ℝ)
    (λ _ → 1ℝ)
identityHasDerivative =
  coordinateHasDerivativeAlong
    (ℝPremetricSpace .snd)
    (idfun ℝ)

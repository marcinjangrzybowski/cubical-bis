module Cubical.HITs.CauchyRealsP.Analysis.Derivative.Basic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

constantHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ)
    (constant : ℝ) →
  IsDerivativeAlong
    source coordinate
    (λ _ → constant)
    (λ _ → 0)
constantHasDerivativeAlong
  source coordinate constant =
    continuousDifferenceFactorGivesDerivative
      source coordinate
      (λ _ → constant)
      (λ _ → 0)
      (λ _ → 0)
      (λ x y →
        subSelf constant
        ∙ sym
            (mulZeroR
              (coordinate y - coordinate x)))
      (λ _ → refl)
      constant-factor-continuous
  where
  constant-factor-continuous :
    isContinuous
      (PremetricProductStr source source)
      (λ _ → 0)
      (snd ℝPremetricSpace)
  constant-factor-continuous point
    .IsContinuousAt.pres≈ ε =
      return
        ( 1
        , λ _ _ → refl∼ 0 ε
        )

coordinateHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ) →
  IsDerivativeAlong
    source coordinate
    coordinate
    (λ _ → 1)
coordinateHasDerivativeAlong
  source coordinate =
    continuousDifferenceFactorGivesDerivative
      source coordinate coordinate
      (λ _ → 1)
      (λ _ → 1)
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
      (λ _ → 1)
      (snd ℝPremetricSpace)
  constant-factor-continuous point
    .IsContinuousAt.pres≈ ε =
      return
        ( 1
        , λ _ _ → refl∼ 1 ε
        )

constantHasDerivative :
  ∀ constant →
  IsDerivative
    (λ _ → constant)
    (λ _ → 0)
constantHasDerivative constant =
  constantHasDerivativeAlong
    (snd ℝPremetricSpace)
    (idfun ℝ) constant

identityHasDerivative :
  IsDerivative
    (idfun ℝ)
    (λ _ → 1)
identityHasDerivative =
  coordinateHasDerivativeAlong
    (snd ℝPremetricSpace)
    (idfun ℝ)

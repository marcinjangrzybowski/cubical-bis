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
open import Cubical.Analysis.Real.Calculus.Derivative.Base

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


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

module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Basic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
  using (sub-self)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
  using (mul-zero-right ; mul-one-right)
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative


constantHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → Real.ℝ)
    (constant : Real.ℝ) →
  IsDerivativeAlong
    source coordinate
    (λ _ → constant)
    (λ _ → Real.ιℚ 0)
constantHasDerivativeAlong source coordinate constant =
  continuousDifferenceFactorGivesDerivative
    source coordinate
    (λ _ → constant)
    (λ _ → Real.ιℚ 0)
    (λ _ → Real.ιℚ 0)
    (λ x y →
      sub-self constant
      ∙ sym
          (mul-zero-right
            (coordinate y Group.- coordinate x)))
    (λ _ → refl)
    constant-factor-continuous
  where
  constant-factor-continuous :
    isContinuous
      (PremetricProductStr source source)
      (λ _ → Real.ιℚ 0)
      (snd Real.ℝPremetricSpace)
  constant-factor-continuous point
    .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ _ → Real.Base.isRefl≈ᶜ (Real.ιℚ 0) ε
      )


coordinateHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → Real.ℝ) →
  IsDerivativeAlong
    source coordinate
    coordinate
    (λ _ → Real.ιℚ 1)
coordinateHasDerivativeAlong source coordinate =
  continuousDifferenceFactorGivesDerivative
    source coordinate coordinate
    (λ _ → Real.ιℚ 1)
    (λ _ → Real.ιℚ 1)
    (λ x y →
      sym
        (mul-one-right
          (coordinate y Group.- coordinate x)))
    (λ _ → refl)
    constant-factor-continuous
  where
  constant-factor-continuous :
    isContinuous
      (PremetricProductStr source source)
      (λ _ → Real.ιℚ 1)
      (snd Real.ℝPremetricSpace)
  constant-factor-continuous point
    .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ _ → Real.Base.isRefl≈ᶜ (Real.ιℚ 1) ε
      )


constantHasDerivative :
  ∀ constant →
  IsDerivative
    (λ _ → constant)
    (λ _ → Real.ιℚ 0)
constantHasDerivative constant =
  constantHasDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (idfun Real.ℝ) constant


identityHasDerivative :
  IsDerivative
    (idfun Real.ℝ)
    (λ _ → Real.ιℚ 1)
identityHasDerivative =
  coordinateHasDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (idfun Real.ℝ)

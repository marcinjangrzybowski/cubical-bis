open import Cubical.Relation.Premetric.Base

module Cubical.Analysis.Completion.Extensionality
  {ℓM} {ℓM'} (M' : PremetricSpace ℓM ℓM') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.UniversalProperty.Base

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as ComparisonDefinition
import Cubical.Relation.Premetric.Completion.UniversalProperty.Extensionality
  as GenericExtensionalityDefinition

module S = SequentialDefinition M'
module SP = SequentialPropertiesDefinition M'
module Comparison = ComparisonDefinition M'

private
  M = M' .fst
  ℓC = ℓ-max ℓM ℓM'

  module PM = PremetricStr (M' .snd)

  sequentialCompletionPresentation : CompletionPresentation M' ℓC ℓC
  sequentialCompletionPresentation .completionSpace =
    SP.ℭ̂ₛPremetricSpace
  sequentialCompletionPresentation .injection = S.ι
  sequentialCompletionPresentation .injection-pres≈ x y ε =
    propBiimpl→Equiv
      (PM.isProp≈ x y ε)
      (S.isProp∼ (S.ι x) ε (S.ι y))
      (S.ι-ι x y ε)
      (Comparison.ι-reflects∼ x y ε)
  sequentialCompletionPresentation .dense = SP.∃approx

open CategoryStructures


-- Continuous maps out of the sequence-backed completion are determined by
-- their values on the original space.  The construction-independent theorem
-- uses only the isometric dense presentation above; no map being compared is
-- transported through a second completion.

module _ {ℓN ℓN'} (N' : PremetricSpace ℓN ℓN') where

  private
    module Direct = GenericExtensionalityDefinition
      M' sequentialCompletionPresentation N'

  continuousExtensionality :
    (f g : S.ℭ̂ₛ → N' .fst) →
    isContinuous (SP.ℭ̂ₛPremetricSpace .snd) f (N' .snd) →
    isContinuous (SP.ℭ̂ₛPremetricSpace .snd) g (N' .snd) →
    (∀ q → f (S.ι q) ≡ g (S.ι q)) →
    f ≡ g
  continuousExtensionality = Direct.continuousMap-ext

  uniformlyContinuousExtensionality :
    (f g : S.ℭ̂ₛ → N' .fst) →
    isUniformlyContinuous
      (SP.ℭ̂ₛPremetricSpace .snd) f (N' .snd) →
    isUniformlyContinuous
      (SP.ℭ̂ₛPremetricSpace .snd) g (N' .snd) →
    (∀ q → f (S.ι q) ≡ g (S.ι q)) →
    f ≡ g
  uniformlyContinuousExtensionality f g f-uc g-uc =
    continuousExtensionality f g
      (isUniformlyContinuous→isContinuous
        (SP.ℭ̂ₛPremetricSpace .snd) f (N' .snd) f-uc)
      (isUniformlyContinuous→isContinuous
        (SP.ℭ̂ₛPremetricSpace .snd) g (N' .snd) g-uc)

  lipschitzExtensionality :
    (f g : S.ℭ̂ₛ → N' .fst) →
    isLipschitz (SP.ℭ̂ₛPremetricSpace .snd) f (N' .snd) →
    isLipschitz (SP.ℭ̂ₛPremetricSpace .snd) g (N' .snd) →
    (∀ q → f (S.ι q) ≡ g (S.ι q)) →
    f ≡ g
  lipschitzExtensionality f g f-lip g-lip =
    continuousExtensionality f g
      (isLipschitz→isContinuous
        (SP.ℭ̂ₛPremetricSpace .snd) f (N' .snd) f-lip)
      (isLipschitz→isContinuous
        (SP.ℭ̂ₛPremetricSpace .snd) g (N' .snd) g-lip)

  nonExpandingExtensionality :
    (f g : S.ℭ̂ₛ → N' .fst) →
    IsNonExpanding (SP.ℭ̂ₛPremetricSpace .snd) f (N' .snd) →
    IsNonExpanding (SP.ℭ̂ₛPremetricSpace .snd) g (N' .snd) →
    (∀ q → f (S.ι q) ≡ g (S.ι q)) →
    f ≡ g
  nonExpandingExtensionality f g f-ne g-ne =
    continuousExtensionality f g
      (isNonExpanding→isContinuous
        (SP.ℭ̂ₛPremetricSpace .snd) f (N' .snd) f-ne)
      (isNonExpanding→isContinuous
        (SP.ℭ̂ₛPremetricSpace .snd) g (N' .snd) g-ne)


-- Iterated forms are the workhorses for algebraic laws.  They deliberately
-- assume only separate continuity, which is what curried lifted operations
-- naturally expose.

module _ {ℓN ℓN'} (N' : PremetricSpace ℓN ℓN') where

  continuousExtensionality₂ :
    (f g : S.ℭ̂ₛ → S.ℭ̂ₛ → N' .fst) →
    (∀ y → isContinuous (SP.ℭ̂ₛPremetricSpace .snd)
      (λ x → f x y) (N' .snd)) →
    (∀ x → isContinuous (SP.ℭ̂ₛPremetricSpace .snd)
      (f x) (N' .snd)) →
    (∀ y → isContinuous (SP.ℭ̂ₛPremetricSpace .snd)
      (λ x → g x y) (N' .snd)) →
    (∀ x → isContinuous (SP.ℭ̂ₛPremetricSpace .snd)
      (g x) (N' .snd)) →
    (∀ p q → f (S.ι p) (S.ι q) ≡ g (S.ι p) (S.ι q)) →
    ∀ x y → f x y ≡ g x y
  continuousExtensionality₂ f g f-cont₁ f-cont₂ g-cont₁ g-cont₂
    on-ι x y =
    funExt⁻
      (continuousExtensionality N'
        (λ u → f u y) (λ u → g u y)
        (f-cont₁ y) (g-cont₁ y)
        λ p →
          funExt⁻
            (continuousExtensionality N'
              (f (S.ι p)) (g (S.ι p))
              (f-cont₂ (S.ι p)) (g-cont₂ (S.ι p))
              (on-ι p))
            y)
      x

  continuousExtensionality₃ :
    (f g : S.ℭ̂ₛ → S.ℭ̂ₛ → S.ℭ̂ₛ → N' .fst) →
    (∀ y z → isContinuous (SP.ℭ̂ₛPremetricSpace .snd)
      (λ x → f x y z) (N' .snd)) →
    (∀ x z → isContinuous (SP.ℭ̂ₛPremetricSpace .snd)
      (λ y → f x y z) (N' .snd)) →
    (∀ x y → isContinuous (SP.ℭ̂ₛPremetricSpace .snd)
      (f x y) (N' .snd)) →
    (∀ y z → isContinuous (SP.ℭ̂ₛPremetricSpace .snd)
      (λ x → g x y z) (N' .snd)) →
    (∀ x z → isContinuous (SP.ℭ̂ₛPremetricSpace .snd)
      (λ y → g x y z) (N' .snd)) →
    (∀ x y → isContinuous (SP.ℭ̂ₛPremetricSpace .snd)
      (g x y) (N' .snd)) →
    (∀ p q r →
      f (S.ι p) (S.ι q) (S.ι r) ≡
      g (S.ι p) (S.ι q) (S.ι r)) →
    ∀ x y z → f x y z ≡ g x y z
  continuousExtensionality₃
    f g f-cont₁ f-cont₂ f-cont₃ g-cont₁ g-cont₂ g-cont₃
    on-ι x y z =
    funExt⁻
      (continuousExtensionality N'
        (λ u → f u y z) (λ u → g u y z)
        (f-cont₁ y z) (g-cont₁ y z)
        λ p →
          funExt⁻
            (continuousExtensionality N'
              (λ v → f (S.ι p) v z)
              (λ v → g (S.ι p) v z)
              (f-cont₂ (S.ι p) z) (g-cont₂ (S.ι p) z)
              λ q →
                funExt⁻
                  (continuousExtensionality N'
                    (f (S.ι p) (S.ι q))
                    (g (S.ι p) (S.ι q))
                    (f-cont₃ (S.ι p) (S.ι q))
                    (g-cont₃ (S.ι p) (S.ι q))
                    (on-ι p q))
                  z)
            y)
      x

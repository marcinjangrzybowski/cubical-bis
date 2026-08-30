module Cubical.Analysis.Real.Algebra.Scalar.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Scalar.Base

open import Cubical.Relation.Premetric.Mappings

open CategoryStructures


private
  composeContinuous :
    (f g : ℝ → ℝ) →
    isContinuous (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd) →
    isContinuous (ℝPremetricSpace .snd) g (ℝPremetricSpace .snd) →
    isContinuous (ℝPremetricSpace .snd) (f ∘ g) (ℝPremetricSpace .snd)
  composeContinuous f g f-cont g-cont =
    snd ((f , f-cont) ∘C (g , g-cont))

  identity-isContinuous : isContinuous
    (ℝPremetricSpace .snd) (idfun ℝ) (ℝPremetricSpace .snd)
  identity-isContinuous = isNonExpanding→isContinuous
    (ℝPremetricSpace .snd) (idfun ℝ) (ℝPremetricSpace .snd)
    (snd (idⁿ {M = ℝPremetricSpace}))

  constant-isContinuous : ∀ c → isContinuous
    (ℝPremetricSpace .snd) (λ (_ : ℝ) → c) (ℝPremetricSpace .snd)
  constant-isContinuous c = isNonExpanding→isContinuous
    (ℝPremetricSpace .snd) (λ (_ : ℝ) → c) (ℝPremetricSpace .snd)
    λ where
      .IsNonExpanding.pres≈ _ _ ε _ → refl∼ c ε


scalar-assoc : ∀ c d x →
  (c ℚR.· d) ⋆ x ≡ c ⋆ (d ⋆ x)
scalar-assoc c d = funExt⁻
  (continuousExtensionality
    ((c ℚR.· d) ⋆_)
    ((c ⋆_) ∘ (d ⋆_))
    (scalar-isContinuous (c ℚR.· d))
    (composeContinuous
      (c ⋆_) (d ⋆_)
      (scalar-isContinuous c) (scalar-isContinuous d))
    λ q →
      scalar-rat (c ℚR.· d) q
      ∙ cong rat (sym (ℚ.·Assoc c d q))
      ∙ sym (scalar-rat c (d ℚR.· q))
      ∙ cong (c ⋆_) (sym (scalar-rat d q)))

scalar-id : ∀ x → 1 ⋆ x ≡ x
scalar-id = funExt⁻
  (continuousExtensionality
    (1 ⋆_) (idfun ℝ)
    (scalar-isContinuous 1) identity-isContinuous
    λ q → scalar-rat 1 q ∙ cong rat (ℚ.·IdL q))

scalar-dist-left : ∀ c d x →
  (c ℚR.+ d) ⋆ x ≡ (c ⋆ x) + (d ⋆ x)
scalar-dist-left c d = funExt⁻
  (continuousExtensionality
    ((c ℚR.+ d) ⋆_)
    (λ x → (c ⋆ x) + (d ⋆ x))
    (scalar-isContinuous (c ℚR.+ d))
    (addOfContinuousIsContinuous
      (ℝPremetricSpace .snd)
      (c ⋆_) (d ⋆_)
      (scalar-isContinuous c) (scalar-isContinuous d))
    λ q →
      scalar-rat (c ℚR.+ d) q
      ∙ cong rat (ℚ.·DistR+ c d q)
      ∙ sym (rat+rat (c ℚR.· q) (d ℚR.· q))
      ∙ cong₂ _+_
          (sym (scalar-rat c q))
          (sym (scalar-rat d q)))

scalar-dist-right : ∀ c x y →
  c ⋆ (x + y) ≡ (c ⋆ x) + (c ⋆ y)
scalar-dist-right c = continuousExtensionality₂
  (λ x y → c ⋆ (x + y))
  (λ x y → (c ⋆ x) + (c ⋆ y))
  (λ y → composeContinuous
    (c ⋆_) (_+ y)
    (scalar-isContinuous c) (add-isContinuous₁ y))
  (λ x → composeContinuous
    (c ⋆_) (x +_)
    (scalar-isContinuous c) (add-isContinuous₂ x))
  (λ y → addOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (c ⋆_) (λ _ → c ⋆ y)
    (scalar-isContinuous c) (constant-isContinuous (c ⋆ y)))
  (λ x → addOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (λ _ → c ⋆ x) (c ⋆_)
    (constant-isContinuous (c ⋆ x)) (scalar-isContinuous c))
  λ p q →
    cong (c ⋆_) (rat+rat p q)
    ∙ scalar-rat c (p ℚR.+ q)
    ∙ cong rat (ℚ.·DistL+ c p q)
    ∙ sym (rat+rat (c ℚR.· p) (c ℚR.· q))
    ∙ cong₂ _+_
        (sym (scalar-rat c p))
        (sym (scalar-rat c q))

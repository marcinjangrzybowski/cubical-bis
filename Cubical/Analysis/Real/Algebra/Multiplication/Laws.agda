module Cubical.Analysis.Real.Algebra.Multiplication.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.UniversalProperty
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication

open import Cubical.Relation.Premetric.Mappings

open CategoryStructures


1ℝ : ℝ
1ℝ = rat 1

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


mulComm : ∀ x y → x · y ≡ y · x
mulComm = continuousExtensionality₂
  _·_ (flip _·_)
  mul-isContinuous₁ mul-isContinuous₂
  mul-isContinuous₂ mul-isContinuous₁
  λ p q →
    mul-rat p q
    ∙ cong rat (ℚ.·Comm p q)
    ∙ sym (mul-rat q p)

mulIdR : ∀ x → x · 1ℝ ≡ x
mulIdR = funExt⁻
  (continuousExtensionality
    (_· 1ℝ) (idfun ℝ)
    (mul-isContinuous₁ 1ℝ) identity-isContinuous
    λ q → mul-rat q 1 ∙ cong rat (ℚ.·IdR q))

mulIdL : ∀ x → 1ℝ · x ≡ x
mulIdL x = mulComm 1ℝ x ∙ mulIdR x

mulAssoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
mulAssoc = continuousExtensionality₃
  (λ x y z → x · (y · z))
  (λ x y z → (x · y) · z)
  (λ y z → mul-isContinuous₁ (y · z))
  (λ x z → composeContinuous
    (x ·_) (_· z) (mul-isContinuous₂ x) (mul-isContinuous₁ z))
  (λ x y → composeContinuous
    (x ·_) (y ·_) (mul-isContinuous₂ x) (mul-isContinuous₂ y))
  (λ y z → composeContinuous
    (_· z) (_· y) (mul-isContinuous₁ z) (mul-isContinuous₁ y))
  (λ x z → composeContinuous
    (_· z) (x ·_) (mul-isContinuous₁ z) (mul-isContinuous₂ x))
  (λ x y → mul-isContinuous₂ (x · y))
  λ p q r →
    cong (rat p ·_) (mul-rat q r)
    ∙ mul-rat p (q ℚ.· r)
    ∙ cong rat (ℚ.·Assoc p q r)
    ∙ sym (mul-rat (p ℚ.· q) r)
    ∙ cong (_· rat r) (sym (mul-rat p q))

mulDistR : ∀ x y z → x · (y + z) ≡ (x · y) + (x · z)
mulDistR = continuousExtensionality₃
  (λ x y z → x · (y + z))
  (λ x y z → (x · y) + (x · z))
  (λ y z → mul-isContinuous₁ (y + z))
  (λ x z → composeContinuous
    (x ·_) (_+ z) (mul-isContinuous₂ x) (add-isContinuous₁ z))
  (λ x y → composeContinuous
    (x ·_) (y +_) (mul-isContinuous₂ x) (add-isContinuous₂ y))
  (λ y z → addOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (_· y) (_· z) (mul-isContinuous₁ y) (mul-isContinuous₁ z))
  (λ x z → addOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (x ·_) (λ _ → x · z)
    (mul-isContinuous₂ x) (constant-isContinuous (x · z)))
  (λ x y → addOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (λ _ → x · y) (x ·_)
    (constant-isContinuous (x · y)) (mul-isContinuous₂ x))
  λ p q r →
    cong (rat p ·_) (rat+rat q r)
    ∙ mul-rat p (q ℚ.+ r)
    ∙ cong rat (ℚ.·DistL+ p q r)
    ∙ sym (rat+rat (p ℚ.· q) (p ℚ.· r))
    ∙ cong₂ _+_ (sym (mul-rat p q)) (sym (mul-rat p r))

mulDistL : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
mulDistL x y z =
  mulComm (x + y) z
  ∙ mulDistR z x y
  ∙ cong₂ _+_ (mulComm z x) (mulComm z y)

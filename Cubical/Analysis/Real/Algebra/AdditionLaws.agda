module Cubical.Analysis.Real.Algebra.AdditionLaws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.Addition

open import Cubical.Relation.Premetric.Mappings

open CategoryStructures


0ℝ : ℝ
0ℝ = rat 0

private
  identityⁿ : NE[ ℝPremetricSpace , ℝPremetricSpace ]
  identityⁿ = idⁿ

  composeNE :
    (f g : ℝ → ℝ) →
    IsNonExpanding (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd) →
    IsNonExpanding (ℝPremetricSpace .snd) g (ℝPremetricSpace .snd) →
    IsNonExpanding (ℝPremetricSpace .snd) (f ∘ g)
      (ℝPremetricSpace .snd)
  composeNE f g f-ne g-ne = snd ((f , f-ne) ∘NE (g , g-ne))

  ne→continuous :
    (f : ℝ → ℝ) →
    IsNonExpanding (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd) →
    isContinuous (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd)
  ne→continuous f = isNonExpanding→isContinuous
    (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd)


addComm : ∀ x y → x + y ≡ y + x
addComm = continuousExtensionality₂
  _+_ (flip _+_)
  add-isContinuous₁ add-isContinuous₂
  add-isContinuous₂ add-isContinuous₁
  λ p q →
    rat+rat p q
    ∙ cong rat (ℚ.+Comm p q)
    ∙ sym (rat+rat q p)

addIdR : ∀ x → x + 0ℝ ≡ x
addIdR = funExt⁻
  (continuousExtensionality
    (_+ 0ℝ) (idfun ℝ)
    (add-isContinuous₁ 0ℝ)
    (ne→continuous (idfun ℝ) (snd identityⁿ))
    λ q → rat+rat q 0 ∙ cong rat (ℚ.+IdR q))

addIdL : ∀ x → 0ℝ + x ≡ x
addIdL x = addComm 0ℝ x ∙ addIdR x

addAssoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
addAssoc = continuousExtensionality₃
  (λ x y z → x + (y + z))
  (λ x y z → (x + y) + z)
  (λ y z → add-isContinuous₁ (y + z))
  (λ x z → ne→continuous _
    (composeNE (x +_) (_+ z)
      (add-isNonExpanding₂ x) (add-isNonExpanding₁ z)))
  (λ x y → ne→continuous _
    (composeNE (x +_) (y +_)
      (add-isNonExpanding₂ x) (add-isNonExpanding₂ y)))
  (λ y z → ne→continuous _
    (composeNE (_+ z) (_+ y)
      (add-isNonExpanding₁ z) (add-isNonExpanding₁ y)))
  (λ x z → ne→continuous _
    (composeNE (_+ z) (x +_)
      (add-isNonExpanding₁ z) (add-isNonExpanding₂ x)))
  (λ x y → add-isContinuous₂ (x + y))
  λ p q r →
    cong (rat p +_) (rat+rat q r)
    ∙ rat+rat p (q ℚ.+ r)
    ∙ cong rat (ℚ.+Assoc p q r)
    ∙ sym (rat+rat (p ℚ.+ q) r)
    ∙ cong (_+ rat r) (sym (rat+rat p q))

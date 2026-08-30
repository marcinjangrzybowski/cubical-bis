module Cubical.Analysis.Real.Algebra.AdditiveGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings

open PositiveRationals

private
  module Pℝ = PremetricStr (ℝPremetricSpace .snd)

  two : ℚ₊
  two = 1 +₊ 1

  twiceRadius : ∀ ε →
    fst (ε +₊ ε) ≡ fst (two ·₊ ε)
  twiceRadius ε = sym
    (ℚ.·DistR+ 1 1 (fst ε)
      ∙ cong₂ ℚ._+_
          (ℚ.·IdL (fst ε)) (ℚ.·IdL (fst ε)))

  inverseSum-isLipschitzWithTwo : IsLipschitzWith
    (ℝPremetricSpace .snd) (λ x → x + (- x))
    (ℝPremetricSpace .snd) two
  inverseSum-isLipschitzWithTwo .IsLipschitzWith.pres≈
    x y ε x∼y =
    Pℝ.subst≈ (x + (- x)) (y + (- y)) (twiceRadius ε)
      (add-pres∼ x y (- x) (- y) ε ε x∼y
        (neg-isNonExpanding .IsNonExpanding.pres≈ x y ε x∼y))

  inverseSum-isContinuous : isContinuous
    (ℝPremetricSpace .snd) (λ x → x + (- x))
    (ℝPremetricSpace .snd)
  inverseSum-isContinuous = isLipschitz→isContinuous
    (ℝPremetricSpace .snd) (λ x → x + (- x))
    (ℝPremetricSpace .snd)
    ∣ two , inverseSum-isLipschitzWithTwo ∣₁

  constantZero-isNonExpanding : IsNonExpanding
    (ℝPremetricSpace .snd) (λ _ → 0ℝ) (ℝPremetricSpace .snd)
  constantZero-isNonExpanding .IsNonExpanding.pres≈ _ _ ε _ =
    refl∼ 0ℝ ε

  constantZero-isContinuous : isContinuous
    (ℝPremetricSpace .snd) (λ _ → 0ℝ) (ℝPremetricSpace .snd)
  constantZero-isContinuous = isNonExpanding→isContinuous
    (ℝPremetricSpace .snd) (λ _ → 0ℝ) (ℝPremetricSpace .snd)
    constantZero-isNonExpanding


addInvR : ∀ x → x + (- x) ≡ 0ℝ
addInvR = funExt⁻
  (continuousExtensionality
    (λ x → x + (- x)) (λ _ → 0ℝ)
    inverseSum-isContinuous constantZero-isContinuous
    λ q →
      cong (rat q +_) (neg-rat q)
      ∙ rat+rat q (ℚ.- q)
      ∙ cong rat (ℚ.+InvR q))

addInvL : ∀ x → (- x) + x ≡ 0ℝ
addInvL x = addComm (- x) x ∙ addInvR x

infixl 6 _-_

_-_ : ℝ → ℝ → ℝ
x - y = x + (- y)

sub-rat : ∀ p q → rat p - rat q ≡ rat (p ℚ.- q)
sub-rat p q = cong (rat p +_) (neg-rat q) ∙ rat+rat p (ℚ.- q)

ℝAbGroup : AbGroup ℓ-zero
ℝAbGroup = makeAbGroup 0ℝ _+_ -_
  isSetℝ addAssoc addIdR addInvR addComm

private
  module ℝGroup = GroupTheory (AbGroup→Group ℝAbGroup)


negInvol : ∀ x → - (- x) ≡ x
negInvol = ℝGroup.invInv

negZero : - 0ℝ ≡ 0ℝ
negZero = ℝGroup.inv1g

negAdd : ∀ x y → - (x + y) ≡ (- x) + (- y)
negAdd x y =
  ℝGroup.invDistr x y
  ∙ addComm (- y) (- x)

subSelf : ∀ x → x - x ≡ 0ℝ
subSelf = addInvR

subZero : ∀ x → x - 0ℝ ≡ x
subZero x = cong (x +_) negZero ∙ addIdR x

zeroSub : ∀ x → 0ℝ - x ≡ - x
zeroSub = addIdL ∘ -_

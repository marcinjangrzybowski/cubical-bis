module Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.AbGroup

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

private
  inverseSumIsLipschitzWith2 :
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → x + (- x))
      (snd ℝPremetricSpace) 2
  inverseSumIsLipschitzWith2
    .IsLipschitzWith.pres≈ x y ε x∼y =
      subst∼ (x + (- x)) (y + (- y))
        {ε = ε +₊ ε} {ε' = 2 ·₊ ε}
        ℚ!
        (addPres∼ x y (- x) (- y) ε ε x∼y
          (negPres∼ x y ε x∼y))

  constantZeroIsNonExpanding :
    IsNonExpanding
      (snd ℝPremetricSpace)
      (λ _ → 0)
      (snd ℝPremetricSpace)
  constantZeroIsNonExpanding
    .IsNonExpanding.pres≈ _ _ ε _ = refl∼ 0 ε

addInvR : ∀ x → x + (- x) ≡ 0
addInvR =
  funExt⁻
    (lipschitzExtensionality ℝPremetricSpace
      (λ x → x + (- x))
      (λ _ → 0)
      ∣ 2 , inverseSumIsLipschitzWith2 ∣₁
      (isNonExpanding→isLipschitz
        (snd ℝPremetricSpace) _
        (snd ℝPremetricSpace) constantZeroIsNonExpanding)
      λ q →
        cong (rat q +_) (neg-rat q)
        ∙ rat+rat q (ℚ.- q)
        ∙ cong rat (ℚ.+InvR q))

addInvL : ∀ x → (- x) + x ≡ 0
addInvL x = addComm (- x) x ∙ addInvR x

infixl 6 _-_

_-_ : ℝ → ℝ → ℝ
x - y = x + (- y)

ℝAbGroup : AbGroup ℓ-zero
ℝAbGroup =
  makeAbGroup 0 _+_ -_
    isSetℝ addAssoc addIdR addInvR addComm

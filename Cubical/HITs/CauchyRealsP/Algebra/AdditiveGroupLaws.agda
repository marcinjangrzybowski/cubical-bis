module Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Properties

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

private
  module ℝGroup = GroupTheory (AbGroup→Group ℝAbGroup)

negInvol : ∀ x → - (- x) ≡ x
negInvol = ℝGroup.invInv

negZero : - 0 ≡ 0
negZero = ℝGroup.inv1g

negAdd : ∀ x y → - (x + y) ≡ (- x) + (- y)
negAdd x y =
  ℝGroup.invDistr x y
  ∙ addComm (- y) (- x)

sub-rat : ∀ p q → rat p - rat q ≡ rat (p ℚ.- q)
sub-rat p q =
  cong (rat p +_) (neg-rat q)
  ∙ rat+rat p (ℚ.- q)
  ∙ cong rat ℚ!

subIsNonExpanding₁ : ∀ y →
  IsNonExpanding
    (snd ℝPremetricSpace) (λ x → x - y) (snd ℝPremetricSpace)
subIsNonExpanding₁ y = addIsNonExpanding₁ (- y)

subIsNonExpanding₂ : ∀ x →
  IsNonExpanding
    (snd ℝPremetricSpace) (λ y → x - y) (snd ℝPremetricSpace)
subIsNonExpanding₂ x
  .IsNonExpanding.pres≈ y y' ε y∼y' =
    addPres∼₂ x (- y) (- y') ε
      (negPres∼ y y' ε y∼y')

subPres∼ : ∀ x x' y y' ε δ
  → x ∼[ ε ] x'
  → y ∼[ δ ] y'
  → (x - y) ∼[ ε +₊ δ ] (x' - y')
subPres∼ x x' y y' ε δ x∼x' y∼y' =
  addPres∼ x x' (- y) (- y') ε δ
    x∼x' (negPres∼ y y' δ y∼y')

subSelf : ∀ x → x - x ≡ 0
subSelf = addInvR

subZeroR : ∀ x → x - 0 ≡ x
subZeroR x =
  cong (x +_) negZero
  ∙ addIdR x

zeroSub : ∀ x → 0 - x ≡ - x
zeroSub x = addIdL (- x)

negSub : ∀ x y → - (x - y) ≡ y - x
negSub x y =
  negAdd x (- y)
  ∙ cong ((- x) +_) (negInvol y)
  ∙ addComm (- x) y

subAddCancel : ∀ x y → (x - y) + y ≡ x
subAddCancel x y =
  sym (addAssoc x (- y) y)
  ∙ cong (x +_) (addInvL y)
  ∙ addIdR x

addSubCancel : ∀ x y → (x + y) - y ≡ x
addSubCancel x y =
  sym (addAssoc x y (- y))
  ∙ cong (x +_) (addInvR y)
  ∙ addIdR x

addCancelL : ∀ x {y z} → x + y ≡ x + z → y ≡ z
addCancelL = ℝGroup.·CancelL

addCancelR : ∀ {x y} z → x + z ≡ y + z → x ≡ y
addCancelR = ℝGroup.·CancelR

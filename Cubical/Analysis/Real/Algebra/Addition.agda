module Cubical.Analysis.Real.Algebra.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation.Monad
import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Analysis.Real.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Analysis.Completion.BinaryNonExpanding
  as BinaryLiftDefinition

private
  module RationalBinary = BinaryNonExpanding
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace
  module RealBinary = BinaryNonExpanding
    ℝPremetricSpace ℝPremetricSpace ℝPremetricSpace
  module AddLift = BinaryLiftDefinition
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingTheory ℚOrderedCommRing

private
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


addℚ : ℚ → ℚ → ℚ
addℚ x y = x ℚ.+ y

private
  addDistanceLeft : ∀ x x' y →
    abs ((x ℚ.+ y) ℚ.- (x' ℚ.+ y)) ≡ abs (x ℚ.- x')
  addDistanceLeft x x' y = cong abs
    (cong₂ ℚ._-_ (ℚ.+Comm x y) (ℚ.+Comm x' y)
      ∙ sym (ℚRing.translatedDifference y x x'))

  addDistanceRight : ∀ x y y' →
    abs ((x ℚ.+ y) ℚ.- (x ℚ.+ y')) ≡ abs (y ℚ.- y')
  addDistanceRight x y y' =
    cong abs (sym (ℚRing.translatedDifference x y y'))

  addℚ₂ : RationalBinary.NE₂[_,_,_]
  addℚ₂ .RationalBinary.NE₂[_,_,_].fun = addℚ
  addℚ₂ .RationalBinary.NE₂[_,_,_].leftNE y
    .IsNonExpanding.pres≈ x x' ε x≈x' =
    subst (ℚ._< fst ε) (sym (addDistanceLeft x x' y)) x≈x'
  addℚ₂ .RationalBinary.NE₂[_,_,_].rightNE x
    .IsNonExpanding.pres≈ y y' ε y≈y' =
    subst (ℚ._< fst ε) (sym (addDistanceRight x y y')) y≈y'

  addℝ₂ : RealBinary.NE₂[_,_,_]
  addℝ₂ = AddLift.liftBinaryNonExpanding addℚ₂


infixl 6 _+_

_+_ : ℝ → ℝ → ℝ
_+_ = RealBinary.NE₂[_,_,_].fun addℝ₂

rat+rat : ∀ p q → rat p + rat q ≡ rat (p ℚ.+ q)
rat+rat = AddLift.liftBinaryNonExpanding-ι addℚ₂

add-isNonExpanding₁ : ∀ y → IsNonExpanding
  (ℝPremetricSpace .snd) (flip _+_ y) (ℝPremetricSpace .snd)
add-isNonExpanding₁ = RealBinary.NE₂[_,_,_].leftNE addℝ₂

add-isNonExpanding₂ : ∀ x → IsNonExpanding
  (ℝPremetricSpace .snd) (x +_) (ℝPremetricSpace .snd)
add-isNonExpanding₂ = RealBinary.NE₂[_,_,_].rightNE addℝ₂

add-isContinuous₁ : ∀ y → isContinuous
  (ℝPremetricSpace .snd) (flip _+_ y) (ℝPremetricSpace .snd)
add-isContinuous₁ y = isNonExpanding→isContinuous
  (ℝPremetricSpace .snd) (flip _+_ y) (ℝPremetricSpace .snd)
  (add-isNonExpanding₁ y)

add-isContinuous₂ : ∀ x → isContinuous
  (ℝPremetricSpace .snd) (x +_) (ℝPremetricSpace .snd)
add-isContinuous₂ x = isNonExpanding→isContinuous
  (ℝPremetricSpace .snd) (x +_) (ℝPremetricSpace .snd)
  (add-isNonExpanding₂ x)

add-pres∼₁ : ∀ x x' y ε →
  x ∼[ ε ] x' → (x + y) ∼[ ε ] (x' + y)
add-pres∼₁ x x' y ε =
  add-isNonExpanding₁ y .IsNonExpanding.pres≈ x x' ε

add-pres∼₂ : ∀ x y y' ε →
  y ∼[ ε ] y' → (x + y) ∼[ ε ] (x + y')
add-pres∼₂ x y y' ε =
  add-isNonExpanding₂ x .IsNonExpanding.pres≈ y y' ε

add-pres∼ : ∀ x x' y y' ε δ →
  x ∼[ ε ] x' → y ∼[ δ ] y' →
  (x + y) ∼[ ε +₊ δ ] (x' + y')
add-pres∼ x x' y y' ε δ x∼x' y∼y' =
  triangle∼ (x + y) (x' + y) (x' + y') ε δ
    (add-pres∼₁ x x' y ε x∼x')
    (add-pres∼₂ x' y y' δ y∼y')


module _
  {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A)
  where

  private
    module Source = PremetricStr source
    module Pℝ = PremetricStr (ℝPremetricSpace .snd)

  addOfContinuousIsContinuous :
    (f g : A → ℝ) →
    isContinuous source f (ℝPremetricSpace .snd) →
    isContinuous source g (ℝPremetricSpace .snd) →
    isContinuous source (λ x → f x + g x) (ℝPremetricSpace .snd)
  addOfContinuousIsContinuous f g f-cont g-cont x
    .IsContinuousAt.pres≈ ε =
    PT.map2
      (λ (δf , f-near) (δg , g-near) →
        ( min₊ δf δg
        , λ y x≈y →
            Pℝ.subst≈ (f x + g x) (f y + g y)
              (/2+/2≡id (fst ε))
              (add-pres∼
                (f x) (f y) (g x) (g y)
                (ε /2₊) (ε /2₊)
                (f-near y
                  (Source.isMonotone≈≤
                    x y (min₊ δf δg) δf
                    (min₊≤L δf δg) x≈y))
                (g-near y
                  (Source.isMonotone≈≤
                    x y (min₊ δf δg) δg
                    (min₊≤R δf δg) x≈y)))
        ))
      (f-cont x .IsContinuousAt.pres≈ (ε /2₊))
      (g-cont x .IsContinuousAt.pres≈ (ε /2₊))

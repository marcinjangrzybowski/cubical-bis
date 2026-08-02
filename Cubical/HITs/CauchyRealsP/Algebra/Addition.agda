module Cubical.HITs.CauchyRealsP.Algebra.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyRealsP.Foundation

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Completion.Properties.Lift

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

private
  module ℚP = PremetricStr (snd ℚPremetricSpace)
  module ℝP = PremetricStr (snd ℝPremetricSpace)

  rationalAddNE₁ : ∀ y →
    IsNonExpanding
      (snd ℚPremetricSpace)
      (λ x → rat (x ℚ.+ y))
      (snd ℝPremetricSpace)
  rationalAddNE₁ y .IsNonExpanding.pres≈ x x' ε x≈x' =
    rat-rat _ _ ε
      (subst (ℚ._< ⟨ ε ⟩₊)
        (cong
          {x = x ℚ.- x'}
          {y = (x ℚ.+ y) ℚ.- (x' ℚ.+ y)}
          abs ℚ!)
        x≈x')

  rationalAddNE₂ : ∀ x →
    IsNonExpanding
      (snd ℚPremetricSpace)
      (λ y → rat (x ℚ.+ y))
      (snd ℝPremetricSpace)
  rationalAddNE₂ x .IsNonExpanding.pres≈ y y' ε y≈y' =
    rat-rat _ _ ε
      (subst (ℚ._< ⟨ ε ⟩₊)
        (cong
          {x = y ℚ.- y'}
          {y = (x ℚ.+ y) ℚ.- (x ℚ.+ y')}
          abs ℚ!)
        y≈y')

  rationalAddLip₁ : ∀ y →
    IsLipschitzWith
      (snd ℚPremetricSpace)
      (λ x → rat (x ℚ.+ y))
      (snd ℝPremetricSpace) 1
  rationalAddLip₁ y =
    isNonExpanding→isLipschitzWith1
      (snd ℚPremetricSpace) _
      (snd ℝPremetricSpace) (rationalAddNE₁ y)

  rationalAddLip₂ : ∀ x →
    IsLipschitzWith
      (snd ℚPremetricSpace)
      (λ y → rat (x ℚ.+ y))
      (snd ℝPremetricSpace) 1
  rationalAddLip₂ x =
    isNonExpanding→isLipschitzWith1
      (snd ℚPremetricSpace) _
      (snd ℝPremetricSpace) (rationalAddNE₂ x)

  addExtension =
    liftLipschitzBinaryWith
      ℚPremetricSpace ℚPremetricSpace ℝPremetricSpace
      isCompleteℝ 1 1
      (λ x y → rat (x ℚ.+ y))
      rationalAddLip₁ rationalAddLip₂

infixl 6 _+_

_+_ : ℝ → ℝ → ℝ
_+_ = fst addExtension

rat+rat : ∀ x y → rat x + rat y ≡ rat (x ℚ.+ y)
rat+rat x y =
  funExt⁻
    (funExt⁻
      (liftBinary∘ι∘ι
        ℚPremetricSpace ℚPremetricSpace ℝPremetricSpace
        isCompleteℝ 1 1
        (λ p q → rat (p ℚ.+ q))
        rationalAddLip₁ rationalAddLip₂)
      x)
    y

addIsNonExpanding₂ : ∀ x →
  IsNonExpanding (snd ℝPremetricSpace) (x +_) (snd ℝPremetricSpace)
addIsNonExpanding₂ x =
  isLipschitzWith1→isNonExpanding
    (snd ℝPremetricSpace) (x +_)
    (snd ℝPremetricSpace) (fst (snd addExtension) x)

addPres∼₂ : ∀ x y y' ε
  → y ∼[ ε ] y'
  → (x + y) ∼[ ε ] (x + y')
addPres∼₂ x y y' ε =
  IsNonExpanding.pres≈ (addIsNonExpanding₂ x) y y' ε

addPres∼₁ : ∀ x x' y ε
  → x ∼[ ε ] x'
  → (x + y) ∼[ ε ] (x' + y)
addPres∼₁ x x' y ε x∼x' =
  ≈→→pointwise ℝ ℝPremetricSpace
    (x +_) (x' +_) ε
    (IsNonExpanding.pres≈ addNE→ x x' ε x∼x')
    y
  where
  addNE→ :
    IsNonExpanding
      (snd ℝPremetricSpace)
      _+_
      (snd (→PremetricSpace ℝ ℝPremetricSpace))
  addNE→ =
    isLipschitzWith1→isNonExpanding
      (snd ℝPremetricSpace) _+_
      (snd (→PremetricSpace ℝ ℝPremetricSpace))
      (snd (snd addExtension))

addIsNonExpanding₁ : ∀ y →
  IsNonExpanding (snd ℝPremetricSpace) (_+ y) (snd ℝPremetricSpace)
IsNonExpanding.pres≈ (addIsNonExpanding₁ y) =
  λ x x' ε → addPres∼₁ x x' y ε

addPres∼ : ∀ x x' y y' ε δ
  → x ∼[ ε ] x'
  → y ∼[ δ ] y'
  → (x + y) ∼[ ε +₊ δ ] (x' + y')
addPres∼ x x' y y' ε δ x∼x' y∼y' =
  triangle∼ (x + y) (x' + y) (x' + y') ε δ
    (addPres∼₁ x x' y ε x∼x')
    (addPres∼₂ x' y y' δ y∼y')

module _
  {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A)
  where
  private
    module Source = PremetricStr source

  addOfContinuousIsContinuous :
    (f g : A → ℝ) →
    isContinuous source f (snd ℝPremetricSpace) →
    isContinuous source g (snd ℝPremetricSpace) →
    isContinuous source
      (λ x → f x + g x)
      (snd ℝPremetricSpace)
  addOfContinuousIsContinuous f g f-cont g-cont x
    .IsContinuousAt.pres≈ ε = do
      δf , f-near ←
        f-cont x .IsContinuousAt.pres≈ (ε /2₊)
      δg , g-near ←
        g-cont x .IsContinuousAt.pres≈ (ε /2₊)
      return
        ( min₊ δf δg
        , λ y x≈y →
            subst∼
              (f x + g x) (f y + g y)
              {ε = (ε /2₊) +₊ (ε /2₊)}
              {ε' = ε}
              (1/2∈ℚ./2+/2≡id (fst ε))
              (addPres∼
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
        )

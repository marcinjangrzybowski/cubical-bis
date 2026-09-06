module Cubical.HITs.CauchyReals.Circle.Winding.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Identities using (injFromNatℚ)
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (idᵘᶜ)

winding-identity : windingNumber idᵘᶜ ≡ 1
winding-identity = injFromNatℚ _ _ (inj-rat _ _
  (windingNumber-lift idᵘᶜ (idfun ℝ)
    ∣ (λ ε → ε , λ x y close → close) ∣₁
    (λ x y → cong (ℝS¹._+ cover (y -ᵣ x)) (sym (cover-β x))
      ∙ sym (cover-add x (y -ᵣ x)) ∙ cong cover ℝ! ∙ cover-β y)
    ∙ -ᵣ-rat₂ 1 0))

constantCircleMap : Circle → UC[ CirclePremetricSpace , CirclePremetricSpace ]
constantCircleMap c = (λ _ → c) , ∣ (idfun _) , preserves ∣₁
  where
  preserves : IsUniformlyContinuousWith (snd CirclePremetricSpace)
    (λ _ → c) (snd CirclePremetricSpace) (idfun _)
  IsUniformlyContinuousWith.pres≈ preserves x y ε _ =
    PremetricStr.isRefl≈ (snd CirclePremetricSpace) c ε

winding-constant : ∀ c → windingNumber (constantCircleMap c) ≡ 0
winding-constant c = injFromNatℚ _ _ (inj-rat _ _
  (windingNumber-lift (constantCircleMap c) (λ _ → 0)
    ∣ (λ ε → ε , λ x y _ → refl∼ 0 ε) ∣₁
    (λ x y → cong (Circle→distCircle c ℝS¹.+_)
      (cong cover (+-ᵣ 0) ∙ cover-zero) ∙ ℝS¹.+IdR _)
    ∙ +-ᵣ 0))

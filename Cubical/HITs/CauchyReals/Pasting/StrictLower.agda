module Cubical.HITs.CauchyReals.Pasting.StrictLower where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous

-- This construction was called `pasting<` in RealPowerBase.
pasteAbove : ∀ b x₀ → b <ᵣ x₀
  → (left : ∀ x → b <ᵣ x → x ≤ᵣ x₀ → ℝ)
  → (right : ∀ x → x₀ ≤ᵣ x → ℝ)
  → ∀ x → b <ᵣ x → ℝ
pasteAbove b x₀ b<x₀ left right x b<x =
  (right (maxᵣ x₀ x) (≤maxᵣ x₀ x)
    +ᵣ left (minᵣ x₀ x)
      (<min-lem x₀ x b b<x₀ b<x)
      (min≤ᵣ x₀ x))
  -ᵣ left x₀ b<x₀ (≤ᵣ-refl x₀)

opaque
  pasteAbove-left : ∀ b x₀ b<x₀ left right
    → left x₀ b<x₀ (≤ᵣ-refl x₀) ≡ right x₀ (≤ᵣ-refl x₀)
    → ∀ x (b<x : b <ᵣ x) (x≤x₀ : x ≤ᵣ x₀)
    → pasteAbove b x₀ b<x₀ left right x b<x ≡ left x b<x x≤x₀
  pasteAbove-left b x₀ b<x₀ left right agrees x b<x x≤x₀ =
    cong₂ _-ᵣ_
      (cong₂ _+ᵣ_
        (cong (uncurry right)
          (Σ≡Prop
            (λ z → isProp≤ᵣ x₀ z)
            (maxᵣComm x₀ x ∙ ≤→maxᵣ x x₀ x≤x₀)))
        (cong (uncurry (uncurry left))
          (Σ≡Prop
            (λ z → isProp≤ᵣ (fst z) x₀)
            (Σ≡Prop
              (λ z → isProp<ᵣ b z)
              (minᵣComm x₀ x ∙ ≤→minᵣ x x₀ x≤x₀)))))
      refl
    ∙ cong
        (_-ᵣ left x₀ b<x₀ (≤ᵣ-refl x₀))
        (+ᵣComm
          (right x₀ (≤ᵣ-refl x₀))
          (left x b<x x≤x₀))
    ∙ cong
        (λ z → (left x b<x x≤x₀ +ᵣ z) -ᵣ
          left x₀ b<x₀ (≤ᵣ-refl x₀))
        (sym agrees)
    ∙ sym (+ᵣAssoc
        (left x b<x x≤x₀)
        (left x₀ b<x₀ (≤ᵣ-refl x₀))
        (-ᵣ left x₀ b<x₀ (≤ᵣ-refl x₀)))
    ∙ cong
        (left x b<x x≤x₀ +ᵣ_)
        (+-ᵣ (left x₀ b<x₀ (≤ᵣ-refl x₀)))
    ∙ +IdR (left x b<x x≤x₀)

  pasteAbove-right : ∀ b x₀ b<x₀ left right
    → left x₀ b<x₀ (≤ᵣ-refl x₀) ≡ right x₀ (≤ᵣ-refl x₀)
    → ∀ x (b<x : b <ᵣ x) (x₀≤x : x₀ ≤ᵣ x)
    → pasteAbove b x₀ b<x₀ left right x b<x ≡ right x x₀≤x
  pasteAbove-right b x₀ b<x₀ left right _ x b<x x₀≤x =
    cong₂ _-ᵣ_
      (cong₂ _+ᵣ_
        (cong (uncurry right)
          (Σ≡Prop
            (λ z → isProp≤ᵣ x₀ z)
            (≤→maxᵣ x₀ x x₀≤x)))
        (cong (uncurry (uncurry left))
          (Σ≡Prop
            (λ z → isProp≤ᵣ (fst z) x₀)
            (Σ≡Prop
              (λ z → isProp<ᵣ b z)
              (≤→minᵣ x₀ x x₀≤x)))))
      refl
    ∙ sym (+ᵣAssoc
        (right x x₀≤x)
        (left x₀ b<x₀ (≤ᵣ-refl x₀))
        (-ᵣ left x₀ b<x₀ (≤ᵣ-refl x₀)))
    ∙ cong
        (right x x₀≤x +ᵣ_)
        (+-ᵣ (left x₀ b<x₀ (≤ᵣ-refl x₀)))
    ∙ +IdR (right x x₀≤x)

pasteAbove-properties : ∀ b x₀ b<x₀ left right
  → left x₀ b<x₀ (≤ᵣ-refl x₀) ≡ right x₀ (≤ᵣ-refl x₀)
  → (∀ x (b<x : b <ᵣ x) (x≤x₀ : x ≤ᵣ x₀) →
      pasteAbove b x₀ b<x₀ left right x b<x ≡ left x b<x x≤x₀)
   × (∀ x (b<x : b <ᵣ x) (x₀≤x : x₀ ≤ᵣ x) →
      pasteAbove b x₀ b<x₀ left right x b<x ≡ right x x₀≤x)
pasteAbove-properties b x₀ b<x₀ left right agrees =
  pasteAbove-left b x₀ b<x₀ left right agrees ,
  pasteAbove-right b x₀ b<x₀ left right agrees

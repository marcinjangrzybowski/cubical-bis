module Cubical.HITs.CauchyReals.Analysis.Pasting.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base

-- This construction was called `pasting` in RealPowerBase.
pasteAt : (x₀ : ℝ)
  → (left : ∀ x → x ≤ᵣ x₀ → ℝ)
  → (right : ∀ x → x₀ ≤ᵣ x → ℝ)
  → ℝ → ℝ
pasteAt x₀ left right x =
  (right (maxᵣ x₀ x) (≤maxᵣ x₀ x)
    +ᵣ left (minᵣ x₀ x) (min≤ᵣ x₀ x))
  -ᵣ left x₀ (≤ᵣ-refl x₀)

opaque
  pasteAt-left : ∀ x₀ left right
    → left x₀ (≤ᵣ-refl x₀) ≡ right x₀ (≤ᵣ-refl x₀)
    → ∀ x (x≤x₀ : x ≤ᵣ x₀)
    → pasteAt x₀ left right x ≡ left x x≤x₀
  pasteAt-left x₀ left right agrees x x≤x₀ =
    cong₂ _-ᵣ_
      (cong₂ _+ᵣ_
        (cong (uncurry right)
          (Σ≡Prop
            (λ z → isProp≤ᵣ x₀ z)
            (maxᵣComm x₀ x ∙ ≤→maxᵣ x x₀ x≤x₀)))
        (cong (uncurry left)
          (Σ≡Prop
            (λ z → isProp≤ᵣ z x₀)
            (minᵣComm x₀ x ∙ ≤→minᵣ x x₀ x≤x₀))))
      refl
    ∙ cong
        (_-ᵣ left x₀ (≤ᵣ-refl x₀))
        (+ᵣComm
          (right x₀ (≤ᵣ-refl x₀))
          (left x x≤x₀))
    ∙ cong
        (λ z → (left x x≤x₀ +ᵣ z) -ᵣ left x₀ (≤ᵣ-refl x₀))
        (sym agrees)
    ∙ sym (+ᵣAssoc
        (left x x≤x₀)
        (left x₀ (≤ᵣ-refl x₀))
        (-ᵣ left x₀ (≤ᵣ-refl x₀)))
    ∙ cong
        (left x x≤x₀ +ᵣ_)
        (+-ᵣ (left x₀ (≤ᵣ-refl x₀)))
    ∙ +IdR (left x x≤x₀)

  pasteAt-right : ∀ x₀ left right
    → left x₀ (≤ᵣ-refl x₀) ≡ right x₀ (≤ᵣ-refl x₀)
    → ∀ x (x₀≤x : x₀ ≤ᵣ x)
    → pasteAt x₀ left right x ≡ right x x₀≤x
  pasteAt-right x₀ left right _ x x₀≤x =
    cong₂ _-ᵣ_
      (cong₂ _+ᵣ_
        (cong (uncurry right)
          (Σ≡Prop
            (λ z → isProp≤ᵣ x₀ z)
            (≤→maxᵣ x₀ x x₀≤x)))
        (cong (uncurry left)
          (Σ≡Prop
            (λ z → isProp≤ᵣ z x₀)
            (≤→minᵣ x₀ x x₀≤x))))
      refl
    ∙ sym (+ᵣAssoc
        (right x x₀≤x)
        (left x₀ (≤ᵣ-refl x₀))
        (-ᵣ left x₀ (≤ᵣ-refl x₀)))
    ∙ cong
        (right x x₀≤x +ᵣ_)
        (+-ᵣ (left x₀ (≤ᵣ-refl x₀)))
    ∙ +IdR (right x x₀≤x)

pasteAt-properties : ∀ x₀ left right
  → left x₀ (≤ᵣ-refl x₀) ≡ right x₀ (≤ᵣ-refl x₀)
  → (∀ x (x≤x₀ : x ≤ᵣ x₀) → pasteAt x₀ left right x ≡ left x x≤x₀)
   × (∀ x (x₀≤x : x₀ ≤ᵣ x) → pasteAt x₀ left right x ≡ right x x₀≤x)
pasteAt-properties x₀ left right agrees =
  pasteAt-left x₀ left right agrees ,
  pasteAt-right x₀ left right agrees

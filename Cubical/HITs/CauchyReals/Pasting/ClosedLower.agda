module Cubical.HITs.CauchyReals.Pasting.ClosedLower where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Pasting

-- This construction was called `pasting≤` in RealPowerBase.
pasteAboveClosed : ∀ b x₀ → b ≤ᵣ x₀
  → (left : ∀ x → b ≤ᵣ x → x ≤ᵣ x₀ → ℝ)
  → (right : ∀ x → x₀ ≤ᵣ x → ℝ)
  → ∀ x → b ≤ᵣ x → ℝ
pasteAboveClosed b x₀ b≤x₀ left right x _ =
  pasteAt x₀ clampedLeft right x
  where
  clampedLeft : ∀ z → z ≤ᵣ x₀ → ℝ
  clampedLeft z z≤x₀ =
    left (maxᵣ b z) (≤maxᵣ b z) (max≤-lem b z x₀ b≤x₀ z≤x₀)

opaque
  pasteAboveClosed-left : ∀ b x₀ b≤x₀ left right
    → left x₀ b≤x₀ (≤ᵣ-refl x₀) ≡ right x₀ (≤ᵣ-refl x₀)
    → ∀ x (b≤x : b ≤ᵣ x) (x≤x₀ : x ≤ᵣ x₀)
    → pasteAboveClosed b x₀ b≤x₀ left right x b≤x ≡
      left x b≤x x≤x₀
  pasteAboveClosed-left b x₀ b≤x₀ left right agrees x b≤x x≤x₀ =
    pasteAt-left x₀ clampedLeft right clampedAgrees x x≤x₀
    ∙ clampedLeft-agrees x b≤x x≤x₀
    where
    clampedLeft : ∀ z → z ≤ᵣ x₀ → ℝ
    clampedLeft z z≤x₀ =
      left (maxᵣ b z) (≤maxᵣ b z) (max≤-lem b z x₀ b≤x₀ z≤x₀)

    clampedLeft-agrees : ∀ z (b≤z : b ≤ᵣ z) (z≤x₀ : z ≤ᵣ x₀) →
      clampedLeft z z≤x₀ ≡ left z b≤z z≤x₀
    clampedLeft-agrees z b≤z z≤x₀ =
      cong (uncurry (uncurry left))
        (Σ≡Prop
          (λ u → isProp≤ᵣ (fst u) x₀)
          (Σ≡Prop
            (λ u → isProp≤ᵣ b u)
            (≤→maxᵣ b z b≤z)))

    clampedAgrees :
      clampedLeft x₀ (≤ᵣ-refl x₀) ≡ right x₀ (≤ᵣ-refl x₀)
    clampedAgrees =
      clampedLeft-agrees x₀ b≤x₀ (≤ᵣ-refl x₀) ∙ agrees

  pasteAboveClosed-right : ∀ b x₀ b≤x₀ left right
    → left x₀ b≤x₀ (≤ᵣ-refl x₀) ≡ right x₀ (≤ᵣ-refl x₀)
    → ∀ x (b≤x : b ≤ᵣ x) (x₀≤x : x₀ ≤ᵣ x)
    → pasteAboveClosed b x₀ b≤x₀ left right x b≤x ≡
      right x x₀≤x
  pasteAboveClosed-right b x₀ b≤x₀ left right agrees x b≤x x₀≤x =
    pasteAt-right x₀ clampedLeft right clampedAgrees x x₀≤x
    where
    clampedLeft : ∀ z → z ≤ᵣ x₀ → ℝ
    clampedLeft z z≤x₀ =
      left (maxᵣ b z) (≤maxᵣ b z) (max≤-lem b z x₀ b≤x₀ z≤x₀)

    clampedAgrees :
      clampedLeft x₀ (≤ᵣ-refl x₀) ≡ right x₀ (≤ᵣ-refl x₀)
    clampedAgrees =
      cong (uncurry (uncurry left))
        (Σ≡Prop
          (λ u → isProp≤ᵣ (fst u) x₀)
          (Σ≡Prop
            (λ u → isProp≤ᵣ b u)
            (≤→maxᵣ b x₀ b≤x₀)))
      ∙ agrees

pasteAboveClosed-properties : ∀ b x₀ b≤x₀ left right
  → left x₀ b≤x₀ (≤ᵣ-refl x₀) ≡ right x₀ (≤ᵣ-refl x₀)
  → (∀ x (b≤x : b ≤ᵣ x) (x≤x₀ : x ≤ᵣ x₀) →
      pasteAboveClosed b x₀ b≤x₀ left right x b≤x ≡ left x b≤x x≤x₀)
   × (∀ x (b≤x : b ≤ᵣ x) (x₀≤x : x₀ ≤ᵣ x) →
      pasteAboveClosed b x₀ b≤x₀ left right x b≤x ≡ right x x₀≤x)
pasteAboveClosed-properties b x₀ b≤x₀ left right agrees =
  pasteAboveClosed-left b x₀ b≤x₀ left right agrees ,
  pasteAboveClosed-right b x₀ b≤x₀ left right agrees


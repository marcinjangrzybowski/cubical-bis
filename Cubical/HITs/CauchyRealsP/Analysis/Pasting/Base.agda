module Cubical.HITs.CauchyRealsP.Analysis.Pasting.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra

-- A proof-relevant presentation of the two pieces is harmless because real
-- order is proposition-valued.  The min/max formula avoids deciding on which
-- side of the junction the input lies.
pasteAt :
  (junction : ℝ) →
  (left : ∀ x → x ≤ℝ junction → ℝ) →
  (right : ∀ x → junction ≤ℝ x → ℝ) →
  ℝ → ℝ
pasteAt junction left right x =
  ( right
      (maxℝ junction x)
      (left≤max junction x)
  + left
      (minℝ junction x)
      (min≤left junction x)
  )
  - left junction (≤ℝ-refl junction)

opaque
  pasteAt-left : ∀ junction
    (left : ∀ x → x ≤ℝ junction → ℝ)
    (right : ∀ x → junction ≤ℝ x → ℝ) →
    left junction (≤ℝ-refl junction)
      ≡ right junction (≤ℝ-refl junction) →
    ∀ x (x≤junction : x ≤ℝ junction) →
    pasteAt junction left right x
      ≡ left x x≤junction
  pasteAt-left
    junction left right agrees x x≤junction =
      cong₂ (λ u v → u - v)
        (cong₂ (λ u v → u + v)
          (cong (uncurry right)
            (Σ≡Prop
              (λ z → isProp≤ℝ junction z)
              (maxComm junction x
              ∙ maxOf≤ x junction x≤junction)))
          (cong (uncurry left)
            (Σ≡Prop
              (λ z → isProp≤ℝ z junction)
              (minComm junction x
              ∙ minOf≤ x junction x≤junction))))
        (refl {x = left junction (≤ℝ-refl junction)})
      ∙ cong
          (λ z → z - left junction (≤ℝ-refl junction))
          (addComm
            (right junction (≤ℝ-refl junction))
            (left x x≤junction))
      ∙ cong
          (λ z →
            (left x x≤junction + z)
              - left junction (≤ℝ-refl junction))
          (sym agrees)
      ∙ addSubCancel
          (left x x≤junction)
          (left junction (≤ℝ-refl junction))

  pasteAt-right : ∀ junction
    (left : ∀ x → x ≤ℝ junction → ℝ)
    (right : ∀ x → junction ≤ℝ x → ℝ) →
    left junction (≤ℝ-refl junction)
      ≡ right junction (≤ℝ-refl junction) →
    ∀ x (junction≤x : junction ≤ℝ x) →
    pasteAt junction left right x
      ≡ right x junction≤x
  pasteAt-right
    junction left right _ x junction≤x =
      cong₂ (λ u v → u - v)
        (cong₂ (λ u v → u + v)
          (cong (uncurry right)
            (Σ≡Prop
              (λ z → isProp≤ℝ junction z)
              (maxOf≤ junction x junction≤x)))
          (cong (uncurry left)
            (Σ≡Prop
              (λ z → isProp≤ℝ z junction)
              (minOf≤ junction x junction≤x))))
        (refl {x = left junction (≤ℝ-refl junction)})
      ∙ addSubCancel
          (right x junction≤x)
          (left junction (≤ℝ-refl junction))

pasteAt-properties : ∀ junction
  (left : ∀ x → x ≤ℝ junction → ℝ)
  (right : ∀ x → junction ≤ℝ x → ℝ) →
  left junction (≤ℝ-refl junction)
    ≡ right junction (≤ℝ-refl junction) →
  (∀ x (x≤junction : x ≤ℝ junction) →
    pasteAt junction left right x ≡ left x x≤junction)
  ×
  (∀ x (junction≤x : junction ≤ℝ x) →
    pasteAt junction left right x ≡ right x junction≤x)
pasteAt-properties junction left right agrees =
  pasteAt-left junction left right agrees
  , pasteAt-right junction left right agrees

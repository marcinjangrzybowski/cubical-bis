module Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base


opaque
  x≤→clampᵣ≡ : ∀ a b x → a ≤ᵣ b → x ≤ᵣ a → clampᵣ a b x ≡ a
  x≤→clampᵣ≡ a b x a≤b x≤a =
    (≤→minᵣ _ _
      (isTrans≡≤ᵣ _ _ _
        (maxᵣComm _ _ ∙ ≤→maxᵣ _ _ x≤a)
        a≤b)
      ∙ maxᵣComm _ _)
    ∙ ≤→maxᵣ _ _ x≤a

  ≤x→clampᵣ≡ : ∀ a b x → a ≤ᵣ b → b ≤ᵣ x → clampᵣ a b x ≡ b
  ≤x→clampᵣ≡ a b x a≤b b≤x =
    cong (flip minᵣ b)
      (≤→maxᵣ _ _ (isTrans≤ᵣ _ _ _ a≤b b≤x))
    ∙ minᵣComm _ _
    ∙ ≤→minᵣ _ _ b≤x

  min-monotone-≤ᵣ : ∀ a x y → x ≤ᵣ y → minᵣ x a ≤ᵣ minᵣ y a
  min-monotone-≤ᵣ a x y x≤y =
    ≤min-lem _ _ _
      (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) x≤y)
      (isTrans≡≤ᵣ _ _ _ (minᵣComm _ _) (min≤ᵣ _ _))

  max-monotone-≤ᵣ : ∀ a x y → x ≤ᵣ y → maxᵣ a x ≤ᵣ maxᵣ a y
  max-monotone-≤ᵣ a x y x≤y =
    max≤-lem _ _ _
      (≤maxᵣ _ _)
      (isTrans≤ᵣ _ _ _ x≤y
        (isTrans≤≡ᵣ _ _ _ (≤maxᵣ _ _) (maxᵣComm _ _)))


clamp-monotone-≤ᵣ : ∀ a b x y → x ≤ᵣ y → clampᵣ a b x ≤ᵣ clampᵣ a b y
clamp-monotone-≤ᵣ a b x y x≤y =
  min-monotone-≤ᵣ b _ _ (max-monotone-≤ᵣ a _ _ x≤y)

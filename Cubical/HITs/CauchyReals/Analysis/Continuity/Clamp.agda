module Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting


clampᵣ∈intervalℙ : ∀ a b → a ≤ᵣ b → ∀ x → clampᵣ a b x ∈ intervalℙ a b
clampᵣ∈intervalℙ a b a≤b x =
  ≤clampᵣ a b x a≤b , clamp≤ᵣ a b x

-- Compatibility name: the endpoints and clamped value are Cauchy reals.
clampᵣ∈ℚintervalℙ : ∀ a b → a ≤ᵣ b → ∀ x → clampᵣ a b x ∈ intervalℙ a b
clampᵣ∈ℚintervalℙ = clampᵣ∈intervalℙ

≡clampᵣ→∈intervalℙ : ∀ a b → a ≤ᵣ b → ∀ x →
  x ≡ clampᵣ a b x → x ∈ intervalℙ a b
≡clampᵣ→∈intervalℙ a b a≤b x p =
  subst-∈ (intervalℙ a b) (sym p) (clampᵣ∈intervalℙ a b a≤b x)


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


opaque
  clampDistᵣ-rat : ∀ L L' x y →
    absᵣ (clampᵣ (rat L) (rat L') y -ᵣ clampᵣ (rat L) (rat L') x)
      ≤ᵣ absᵣ (y -ᵣ x)
  clampDistᵣ-rat L L' =
    ≤Cont₂
      (cont∘₂ IsContinuousAbsᵣ
        (IsContinuous-₂∘
          (asIsContinuous₂-snd _ (IsContinuousClamp (rat L) (rat L')))
          (asIsContinuous₂-fst _ (IsContinuousClamp (rat L) (rat L')))))
      (cont∘₂ IsContinuousAbsᵣ (snd IsContinuous-₂ , fst IsContinuous-₂))
      λ u u' →
        subst2 _≤ᵣ_
          (sym (cong rat
            (sym (ℚ.abs'≡abs (ℚ.clamp L L' u' ℚ.- ℚ.clamp L L' u)))) ∙ ℚℝ!)
          (sym (absᵣ-rat _) ∙ cong absᵣ (sym (-ᵣ-rat₂ _ _)))
          (≤ℚ→≤ᵣ _ _ (ℚ.clampDist L L' u u'))

  -- Compatibility name retained for existing inverse-module consumers.
  clampDistᵣ' : ∀ L L' x y →
    absᵣ (clampᵣ (rat L) (rat L') y -ᵣ clampᵣ (rat L) (rat L') x)
      ≤ᵣ absᵣ (y -ᵣ x)
  clampDistᵣ' = clampDistᵣ-rat

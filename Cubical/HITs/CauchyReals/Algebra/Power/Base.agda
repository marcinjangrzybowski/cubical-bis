module Cubical.HITs.CauchyReals.Algebra.Power.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting
open import Cubical.HITs.CauchyReals.Foundation.Rationals

0^ⁿ : ∀ n → 0 ^ⁿ (suc n) ≡ 0
0^ⁿ n = 0LeftAnnihilatesᵣ _
  where
  0LeftAnnihilatesᵣ : ∀ x → 0 ·ᵣ x ≡ 0
  0LeftAnnihilatesᵣ = ≡Continuous _ _
    (IsContinuous·ᵣL 0)
    (IsContinuousConst 0)
    (λ q → sym (rat·ᵣrat 0 q) ∙ cong rat (ℚ.·AnnihilL q))

1^ⁿ : ∀ n → 1 ^ⁿ n ≡ 1
1^ⁿ zero = refl
1^ⁿ (suc n) = ·IdLᵣ _ ∙ 1^ⁿ n

^ⁿ-odd : ∀ n x → -ᵣ (x ^ⁿ suc (n ℕ.· 2)) ≡ ((-ᵣ x) ^ⁿ suc (n ℕ.· 2))
^ⁿ-even : ∀ n x → (x ^ⁿ (n ℕ.· 2)) ≡ ((-ᵣ x) ^ⁿ (n ℕ.· 2))

^ⁿ-even zero x = refl
^ⁿ-even (suc n) x = ·ᵣAssoc _ _ _ ∙ cong₂ _·ᵣ_ (sym (-ᵣ·-ᵣ x x)) (^ⁿ-even n x)
  ∙ sym (·ᵣAssoc _ _ _)

^ⁿ-odd n x = sym (-ᵣ· _ _) ∙ cong ((-ᵣ x) ·ᵣ_) (^ⁿ-even n x)

x·x≡∣x∣·∣x∣ : ∀ x → x ·ᵣ x ≡ absᵣ x ·ᵣ absᵣ x
x·x≡∣x∣·∣x∣ x = ≡Cont₂
  (cont₂·₂ᵣ
   (asIsContinuous₂-fst _ IsContinuousId) (asIsContinuous₂-fst _ IsContinuousId))
  (cont₂·₂ᵣ
   (asIsContinuous₂-fst _ IsContinuousAbsᵣ) (asIsContinuous₂-fst _ IsContinuousAbsᵣ))
   (λ x x' → ℚℝ! ∙∙ cong rat (sym (abs²≡² x)) ∙∙
     ((λ i → rat (ℚ.abs'≡abs x i ℚ.· ℚ.abs'≡abs x i)) ∙ ℚℝ!))
  x x

IsContinuous^ⁿ : ∀ n → IsContinuous (_^ⁿ n)
IsContinuous^ⁿ zero = IsContinuousConst _
IsContinuous^ⁿ (suc n) =
  cont₂·ᵣ _ _ IsContinuousId (IsContinuous^ⁿ n)

0≤ᵣx² : ∀ x → 0 ≤ᵣ (x ^ⁿ 2)
0≤ᵣx² = ≤Cont
  (IsContinuousConst 0)
  (IsContinuous^ⁿ 2)
  (λ q → isTrans≤≡ᵣ _ _ _
    (≤ℚ→≤ᵣ _ _ (0≤² q))
    (cong rat ℚ! ∙ sym (^ⁿ-ℚ^ⁿ 2 q)))

absᵣ^ⁿ : ∀ x n → absᵣ (x ^ⁿ n) ≡ (absᵣ x ^ⁿ n)
absᵣ^ⁿ x zero = absᵣ-rat 1
absᵣ^ⁿ x (suc n) =
  ·absᵣ _ _ ∙ cong₂ _·ᵣ_ refl (absᵣ^ⁿ x n)

abs[x^²ⁿ] : ∀ n x → x ^ⁿ (n ℕ.· 2) ≡ absᵣ (x ^ⁿ (n ℕ.· 2))
abs[x^²ⁿ] zero x = sym (absᵣ-rat 1)
abs[x^²ⁿ] (suc n) x =
    ·ᵣAssoc _ _ _
  ∙ cong₂ _·ᵣ_ (x·x≡∣x∣·∣x∣ x) (abs[x^²ⁿ] n x)
  ∙ sym (·ᵣAssoc _ _ _)
  ∙ cong₂ _·ᵣ_ refl (sym (·absᵣ _ _))
  ∙ sym (·absᵣ _ _)

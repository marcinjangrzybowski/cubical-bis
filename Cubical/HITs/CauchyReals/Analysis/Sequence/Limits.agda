module Cubical.HITs.CauchyReals.Analysis.Sequence.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels using (isPropΠ)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base using (𝕣-lim')
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals

private
  half+half≡ : (ε : ℚ₊) → fst (ε /2₊) ℚ.+ fst (ε /2₊) ≡ fst ε
  half+half≡ ε = ℚ!!

isCauchySequence-∘+ : ∀ s k
  → IsCauchySequence' s
  → IsCauchySequence' (s ∘ (k ℕ.+_))
isCauchySequence-∘+ s k =
  map-snd (λ X m n <n <m →
    X (k ℕ.+ m) (k ℕ.+ n)
      (ℕ.≤-trans <n ℕ.≤SumRight)
      (ℕ.≤-trans <m ℕ.≤SumRight)) ∘_

fromCauchySequence'₁-≡-lem : ∀ s ics ics' →
  fromCauchySequence'₁ s ics ≡ fromCauchySequence'₁ s ics'
fromCauchySequence'₁-≡-lem s =
  PT.elim2 (λ _ _ → isSetℝ _ _)
   (fromCauchySequence'-≡-lem s)

fromCauchySequence'₁-≡ : ∀ s s' ics ics' →
  (∀ n → s n ≡ s' n) →
  fromCauchySequence'₁ s ics ≡ fromCauchySequence'₁ s' ics'
fromCauchySequence'₁-≡ s s' ics ics' p = PT.elim2
  (λ ics ics' → isSetℝ
      (fromCauchySequence'₁ s ics)
      (fromCauchySequence'₁ s' ics'))
  (λ ics ics' → fromCauchySequence'-≡ s s' ics ics' p)
  ics ics'

lim-const : ∀ x y → lim (const x) y ≡ x
lim-const = Elimℝ-Prop.go elimProp
 where
 elimProp : Elimℝ-Prop _
 elimProp .Elimℝ-Prop.ratA x _ =
   eqℝ _ _ λ ε →
     lim-rat _ _ _ (ε /2₊) _ _ (refl∼ _ (ℚ.<→ℚ₊ (fst (ε /2₊)) (fst ε) (/2₊<id ε)) )
 elimProp .Elimℝ-Prop.limA x p x₁ y =
   eqℝ _ _ λ ε →
     lim-lim _ _ _ ((ε /2₊) /2₊) ((ε /2₊) /2₊) _ _
       (subst ℚ.0<_
          (cong (ℚ._-_ (fst ε)) (sym (half+half≡ (ε /2₊))))
          (snd (ℚ.<→ℚ₊ (fst (ε /2₊)) (fst ε) (/2₊<id ε))))
       (sym∼ _ _ _
        (𝕣-lim' _ _ _ ((ε /2₊) /2₊) _
        (snd ((ℚ.<→ℚ₊ (fst ((ε /2₊) /2₊)) (fst ε ℚ.- (fst ((ε /2₊) /2₊) ℚ.+ fst ((ε /2₊) /2₊)))
         ((subst {x = fst (ε /2₊)} (fst ((ε /2₊) /2₊) ℚ.<_)
           (sym (Rℚ.plusMinus _ _) ∙
             cong₂ (ℚ._-_) (half+half≡ ε) (sym (half+half≡ (ε /2₊))))
            (/2₊<id (ε /2₊)))))))
         (refl∼ _ _)))
 elimProp .Elimℝ-Prop.isPropA _ = isPropΠ λ _ → isSetℝ _ _

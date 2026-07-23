module Cubical.HITs.CauchyReals.Analysis.Continuity.Limit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.Tactics.CauchyReals.ExpressionLifting


opaque
 unfolding maxᵣ

 ≤lim : ∀ r x y → (∀ δ → rat r ≤ᵣ x δ) → rat r ≤ᵣ lim x y
 ≤lim r x y p = ≡→≤ᵣ $
   snd (NonExpanding₂.β-rat-lim' maxR r x y) ∙
     congLim _ _ _ _ (≤ᵣ→≡ ∘ p)

 limConstRat : ∀ x y → lim (λ _ → rat x) y ≡ rat x
 limConstRat x y = eqℝ _ _ λ ε →
   lim-rat _ _ _ (ε /2₊) _ <≤ℚ! (refl∼ _ _)

 lim≤ : ∀ r x y → (∀ δ → x δ ≤ᵣ rat r) → lim x y ≤ᵣ rat r
 lim≤ r x y p = ≡→≤ᵣ $
   maxᵣComm (lim x y) (rat r) ∙
   snd (NonExpanding₂.β-rat-lim' maxR r x y) ∙
   congLim' _ _ _ (λ δ → maxᵣComm (rat r) (x δ) ∙ ≤ᵣ→≡ (p δ)) ∙
   limConstRat _ _

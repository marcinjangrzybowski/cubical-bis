module Cubical.HITs.CauchyReals.Foundation.Order.Density where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base


opaque

 <ᵣ→Δ : ∀ x y → x <ᵣ y →
   ∃[ δ ∈ ℚ₊ ] (rat (fst δ) <ᵣ y +ᵣ (-ᵣ x))
 <ᵣ→Δ x y = PT.map
   (λ ((q , q') , (a , a' , a'')) →
     (ℚ.<→ℚ₊ q q' a') /2₊ ,
       let -q≤-x = -ᵣ≤ᵣ _ _ a
           q'-q≤y-x = ≤ᵣMonotone+ᵣ _ _ _ _ a'' -q≤-x
           Δ/2<q'-q : fst (ℚ.<→ℚ₊ q q' a' /2₊) ℚ.< q' ℚ.- q
           Δ/2<q'-q = <≤ℚ![ a' ]
       in isTrans<≤ᵣ _ _ _
            (<ℚ→<ᵣ _ _ Δ/2<q'-q)
            (isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat₂ _ _)) q'-q≤y-x))
   ∘S fst (<ᵣ-impl _ _)

module Cubical.HITs.CauchyReals.Foundation.Order.RationalBounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (pos)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals


opaque
 unfolding absᵣ _<ᵣ_

 abs'q≤Δ₁ : ∀ q n → absᵣ (rat q) <ᵣ rat [ pos (suc n) / 1+ 0 ]
   → ℚ.abs' q ℚ.≤ ([ pos (suc (suc n)) / 1 ] ℚ.- [ 1 / 4 ])
 abs'q≤Δ₁ q n q<n =
   ℚ.isTrans≤ (ℚ.abs' q) (fromNat (suc n)) _
     (ℚ.<Weaken≤ _ _ (<ᵣ→<ℚ _ _ q<n))
     (subst2 ℚ._≤_ (ℚ.+IdR _) ℚ!
       (ℚ.≤-o+ 0 [ 3 / 4 ] (fromNat (suc n))
         (𝟚.toWitness {Q = ℚ.≤Dec 0 [ 3 / 4 ]} _)))

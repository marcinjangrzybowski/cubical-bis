module Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base


absᵣNonPos : ∀ (x : ℝ) → x ≤ᵣ 0 → absᵣ x ≡ -ᵣ x
absᵣNonPos x p = abs-max x ∙ ≤ᵣ→≡ z
  where
  z : x ≤ᵣ -ᵣ x
  z = isTrans≤ᵣ _ _ _ p
    (isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat _)) (-ᵣ≤ᵣ _ _ p))


opaque
  unfolding _<ᵣ_ absᵣ -ᵣ_

  absᵣNeg : ∀ (x : ℝ) → x <ᵣ 0 → absᵣ x ≡ -ᵣ x
  absᵣNeg x x<0 = -absᵣ x ∙ absᵣPos _ (-ᵣ<ᵣ x _ x<0)

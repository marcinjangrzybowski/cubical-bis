module Cubical.HITs.CauchyReals.Foundation.Order.Positive where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base

-ℝ₊<ℝ₊ : ∀ x y → -ᵣ fst x <ᵣ fst y
-ℝ₊<ℝ₊ x y =
  isTrans<ᵣ _ _ _
    (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (snd x)) (-ᵣ-rat 0))
    (snd y)

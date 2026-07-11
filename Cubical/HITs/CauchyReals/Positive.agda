module Cubical.HITs.CauchyReals.Positive where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.RationalsImports
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous

-ℝ₊<ℝ₊ : ∀ x y → -ᵣ fst x <ᵣ fst y
-ℝ₊<ℝ₊ x y =
  isTrans<ᵣ _ _ _
    (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (snd x)) (-ᵣ-rat 0))
    (snd y)

{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Core.Vectors where

open import Cubical.Foundations.Prelude using (Level; Type)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

-- Small finite profiles share these constructors regardless of whether a
-- coordinate contains a real amount, a probability, a trade, or a state.
two : ∀ {ℓ} {A : Type ℓ} → A → A → Fin 2 → A
two a b zero = a
two a b (suc zero) = b

three : ∀ {ℓ} {A : Type ℓ} → A → A → A → Fin 3 → A
three a b c zero = a
three a b c (suc zero) = b
three a b c (suc (suc zero)) = c

four : ∀ {ℓ} {A : Type ℓ} → A → A → A → A → Fin 4 → A
four a b c d zero = a
four a b c d (suc zero) = b
four a b c d (suc (suc zero)) = c
four a b c d (suc (suc (suc zero))) = d

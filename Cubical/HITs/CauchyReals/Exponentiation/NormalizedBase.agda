module Cubical.HITs.CauchyReals.Exponentiation.NormalizedBase where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Exponentiation.RealPowerCalculus

opaque
  normalizedBase : (a : ℝ₊) → 1 <ᵣ fst a → ℝ₊
  normalizedBase a 1<a =
    a ^ᵣ fst (invℝ₊ (ln a , 1<a→0<ln[a] a 1<a))

  normalizedBase-spec : ∀ a (1<a : 1 <ᵣ fst a) →
    normalizedBase a 1<a ≡
      a ^ᵣ fst (invℝ₊ (ln a , 1<a→0<ln[a] a 1<a))
  normalizedBase-spec a 1<a = refl

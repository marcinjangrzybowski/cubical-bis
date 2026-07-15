module Cubical.HITs.CauchyReals.Exponentiation.Normalized.Base where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Calculus

opaque
  normalizedBase : (a : ℝ₊) → 1 <ᵣ fst a → ℝ₊
  normalizedBase a 1<a =
    a ^ᵣ fst (invℝ₊ (ln a , 1<a→0<ln[a] a 1<a))

  normalizedBase-spec : ∀ a (1<a : 1 <ᵣ fst a) →
    normalizedBase a 1<a ≡
      a ^ᵣ fst (invℝ₊ (ln a , 1<a→0<ln[a] a 1<a))
  normalizedBase-spec a 1<a = refl

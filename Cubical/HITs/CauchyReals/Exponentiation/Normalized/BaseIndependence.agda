module Cubical.HITs.CauchyReals.Exponentiation.Normalized.BaseIndependence where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Order using (ln-injective)
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.Base
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.BaseLaw

opaque
  normalizedBase-independent :
    ∀ a (1<a : 1 <ᵣ fst a) a' (1<a' : 1 <ᵣ fst a') →
    normalizedBase a 1<a ≡ normalizedBase a' 1<a'
  normalizedBase-independent a 1<a a' 1<a' =
    ln-injective _ _
      (ln-normalizedBase a 1<a ∙ sym (ln-normalizedBase a' 1<a'))

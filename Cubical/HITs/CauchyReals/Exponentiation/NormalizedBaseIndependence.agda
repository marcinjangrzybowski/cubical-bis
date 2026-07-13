module Cubical.HITs.CauchyReals.Exponentiation.NormalizedBaseIndependence where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.RationalsImports
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm using (ln-injective)
open import Cubical.HITs.CauchyReals.Exponentiation.NormalizedBase
open import Cubical.HITs.CauchyReals.Exponentiation.NormalizedBaseLaw

opaque
  normalizedBase-independent :
    ∀ a (1<a : 1 <ᵣ fst a) a' (1<a' : 1 <ᵣ fst a') →
    normalizedBase a 1<a ≡ normalizedBase a' 1<a'
  normalizedBase-independent a 1<a a' 1<a' =
    ln-injective _ _
      (ln-normalizedBase a 1<a ∙ sym (ln-normalizedBase a' 1<a'))

module Cubical.HITs.CauchyReals.Exponentiation.NormalizedExponentialLogLaw where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.ExponentiationMore using (ln)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPowerCalculus
open import Cubical.HITs.CauchyReals.Exponentiation.NormalizedExponentialBase public

opaque
  ln-realExp : ∀ x → ln (realExp x) ≡ x
  ln-realExp x =
    ln-realPower eBase x
    ∙ cong (x ·ᵣ_) ln-eBase
    ∙ ·IdR x

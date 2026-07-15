module Cubical.HITs.CauchyReals.Exponentiation.Normalized.Exponential.LogLaw where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition using (ln)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Calculus
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.Exponential.Base public

opaque
  ln-realExp : ∀ x → ln (realExp x) ≡ x
  ln-realExp x =
    ln-realPower eBase x
    ∙ cong (x ·ᵣ_) ln-eBase
    ∙ ·IdR x

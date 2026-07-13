module Cubical.HITs.CauchyReals.Exponentiation.NormalizedExponentialInverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order using (ℝ₊)
open import Cubical.HITs.CauchyReals.ExponentiationMore using (ln)
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm using (ln-injective)
open import Cubical.HITs.CauchyReals.Exponentiation.NormalizedExponentialLogLaw public

opaque
  realExp-ln : ∀ x → realExp (ln x) ≡ x
  realExp-ln x =
    ln-injective (realExp (ln x)) x (ln-realExp (ln x))

expLogIso : Iso ℝ ℝ₊
expLogIso .Iso.fun = realExp
expLogIso .Iso.inv = ln
expLogIso .Iso.sec = realExp-ln
expLogIso .Iso.ret = ln-realExp

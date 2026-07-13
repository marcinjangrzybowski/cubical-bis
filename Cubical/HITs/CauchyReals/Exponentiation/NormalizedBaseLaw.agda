module Cubical.HITs.CauchyReals.Exponentiation.NormalizedBaseLaw where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Exponentiation.RealPowerCalculus
open import Cubical.HITs.CauchyReals.Exponentiation.NormalizedBase

opaque
  normalizedBase-logPower : ∀ a (1<a : 1 <ᵣ fst a) →
    ln (normalizedBase a 1<a) ≡
      fst (invℝ₊ (ln a , 1<a→0<ln[a] a 1<a)) ·ᵣ ln a
  normalizedBase-logPower a 1<a =
    cong ln (normalizedBase-spec a 1<a)
    ∙ ln-realPower a (fst (invℝ₊ (ln a , 1<a→0<ln[a] a 1<a)))

  normalizedBase-logCancel : ∀ a (1<a : 1 <ᵣ fst a) →
    fst (invℝ₊ (ln a , 1<a→0<ln[a] a 1<a)) ·ᵣ ln a ≡ 1
  normalizedBase-logCancel a 1<a =
    ·ᵣComm _ _ ∙ x·invℝ₊[x] (ln a , 1<a→0<ln[a] a 1<a)

  ln-normalizedBase : ∀ a (1<a : 1 <ᵣ fst a) →
    ln (normalizedBase a 1<a) ≡ 1
  ln-normalizedBase a 1<a =
    normalizedBase-logPower a 1<a ∙ normalizedBase-logCancel a 1<a

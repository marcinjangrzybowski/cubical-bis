module Cubical.HITs.CauchyReals.Exponentiation.Normalized.BaseLaw where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Calculus
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.Base

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

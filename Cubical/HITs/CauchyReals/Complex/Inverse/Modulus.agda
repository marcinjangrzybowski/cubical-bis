module Cubical.HITs.CauchyReals.Complex.Inverse.Modulus where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Inverse using
  (_＃_; invℝ; x·invℝ[x])

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Positive
open import Cubical.HITs.CauchyReals.Complex.Inverse.Base


private
  opaque
    inverseFromProduct : (a b : ℝ) → (0#a : 0 ＃ a) →
      a ·ᵣ b ≡ 1 →
      b ≡ invℝ a 0#a
    inverseFromProduct a b 0#a product =
      sym (Rℝ.·IdR b)
      ∙ cong (b ·ᵣ_)
          (sym (x·invℝ[x] a 0#a))
      ∙ ·ᵣAssoc b a (invℝ a 0#a)
      ∙ cong (_·ᵣ invℝ a 0#a)
          (·ᵣComm b a)
      ∙ cong (_·ᵣ invℝ a 0#a)
          product
      ∙ Rℝ.·IdL (invℝ a 0#a)


opaque
  modulus-invℂ : (z : ℂ) → (0#z : 0ℂ #ℂ z) →
    modulus (invℂ z 0#z) ≡
    invℝ (modulus z) (0#modulus 0#z)
  modulus-invℂ z 0#z =
    inverseFromProduct
      (modulus z)
      (modulus (invℂ z 0#z))
      (0#modulus 0#z)
      (sym (modulus-mul z (invℂ z 0#z))
       ∙ cong modulus (·invℂ z 0#z)
       ∙ modulus1)

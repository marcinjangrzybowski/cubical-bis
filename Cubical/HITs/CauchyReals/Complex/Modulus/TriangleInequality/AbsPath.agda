module Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality.AbsPath where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Triangle


opaque
  modulusAbsPath : ∀ z w →
    modulus (absComplex z) +ᵣ modulus (absComplex w) ≡
    modulus z +ᵣ modulus w
  modulusAbsPath z w = cong₂ _+ᵣ_
    (modulus-absComplex z) (modulus-absComplex w)

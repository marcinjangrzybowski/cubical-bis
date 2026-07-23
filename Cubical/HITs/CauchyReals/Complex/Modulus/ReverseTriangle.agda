module Cubical.HITs.CauchyReals.Complex.Modulus.ReverseTriangle where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base
open import Cubical.HITs.CauchyReals.Algebra.Ring

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


opaque
  difference-reconstruct : ∀ z w → (z -ℂ w) +ℂ w ≡ z
  difference-reconstruct _ _ = ℂ≡ ℝ! ℝ!


opaque
  reconstructedTriangle : ∀ z w →
    modulus z ≤ᵣ modulus (z -ℂ w) +ᵣ modulus w
  reconstructedTriangle z w = subst
    (_≤ᵣ modulus (z -ℂ w) +ᵣ modulus w)
    (cong modulus (difference-reconstruct z w))
    (modulus-triangle (z -ℂ w) w)


opaque
  modulus-reverse-triangle : ∀ z w →
    modulus z -ᵣ modulus w ≤ᵣ modulus (z -ℂ w)
  modulus-reverse-triangle z w =
    isTrans≤≡ᵣ _ _ _
      (≤ᵣ-+o _ _ (-ᵣ (modulus w))
        (reconstructedTriangle z w))
      (Rℝ.plusMinus (modulus (z -ℂ w)) (modulus w))

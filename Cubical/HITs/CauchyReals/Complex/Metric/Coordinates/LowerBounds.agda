module Cubical.HITs.CauchyReals.Complex.Metric.Coordinates.LowerBounds where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Triangle

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


opaque
  abs-re≤modulus : ∀ z → absᵣ (re z) ≤ᵣ modulus z
  abs-re≤modulus z = isTrans≡≤ᵣ _ _ _
    (sym (modulus-fromℝ (re z)))
    (modulusMonotoneAbsCoords (fromℝ (re z)) z
      (≤ᵣ-refl (absᵣ (re z)))
      (isTrans≡≤ᵣ _ _ _ absᵣ0 (0≤absᵣ (im z))))


opaque
  abs-im≤modulus : ∀ z → absᵣ (im z) ≤ᵣ modulus z
  abs-im≤modulus z = isTrans≡≤ᵣ _ _ _
    (sym (modulus-imag (im z)))
    (modulusMonotoneAbsCoords (imagℂ (im z)) z
      (isTrans≡≤ᵣ _ _ _ absᵣ0 (0≤absᵣ (re z)))
      (≤ᵣ-refl (absᵣ (im z))))


opaque
  abs-re-difference≤modulus : ∀ z w →
    absᵣ (re z -ᵣ re w) ≤ᵣ modulus (z -ℂ w)
  abs-re-difference≤modulus z w = isTrans≡≤ᵣ _ _ _
    (cong absᵣ (ℝ!))
    (abs-re≤modulus (z -ℂ w))


opaque
  abs-im-difference≤modulus : ∀ z w →
    absᵣ (im z -ᵣ im w) ≤ᵣ modulus (z -ℂ w)
  abs-im-difference≤modulus z w = isTrans≡≤ᵣ _ _ _
    (cong absᵣ (ℝ!))
    (abs-im≤modulus (z -ℂ w))

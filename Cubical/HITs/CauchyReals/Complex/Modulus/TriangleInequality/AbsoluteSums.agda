module Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality.AbsoluteSums where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base


opaque
  absSumNonNeg : ∀ a b → 0 ≤ᵣ absᵣ a +ᵣ absᵣ b
  absSumNonNeg a b = isTrans≡≤ᵣ _ _ _
    (sym (+ᵣ-rat 0 0))
    (≤ᵣMonotone+ᵣ _ _ _ _ (0≤absᵣ a) (0≤absᵣ b))


opaque
  absSumBound : ∀ a b → absᵣ (a +ᵣ b) ≤ᵣ absᵣ (absᵣ a +ᵣ absᵣ b)
  absSumBound a b = isTrans≤≡ᵣ _ _ _
    (absᵣ-triangle a b)
    (sym (absᵣNonNeg _ (absSumNonNeg a b)))

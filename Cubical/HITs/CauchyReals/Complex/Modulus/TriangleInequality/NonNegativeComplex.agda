module Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality.NonNegativeComplex where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Minkowski


opaque
  modulusTriangleNonNegativeCoordinates : ∀ z w →
    0 ≤ᵣ re z → 0 ≤ᵣ im z → 0 ≤ᵣ re w → 0 ≤ᵣ im w →
    modulus (z +ℂ w) ≤ᵣ modulus z +ᵣ modulus w
  modulusTriangleNonNegativeCoordinates (a , b) (c , d)
    0≤a 0≤b 0≤c 0≤d =
    modulusTriangleNonNeg a b c d 0≤a 0≤b 0≤c 0≤d


NonNegativeCoordinates : ℂ → Type₀
NonNegativeCoordinates z = (0 ≤ᵣ re z) × (0 ≤ᵣ im z)


FirstQuadrantℂ : Type₀
FirstQuadrantℂ = Σ[ z ∈ ℂ ] NonNegativeCoordinates z


opaque
  firstQuadrantTriangle : ∀ (z w : FirstQuadrantℂ) →
    modulus (fst z +ℂ fst w) ≤ᵣ modulus (fst z) +ᵣ modulus (fst w)
  firstQuadrantTriangle (z , 0≤re-z , 0≤im-z)
    (w , 0≤re-w , 0≤im-w) =
    modulusTriangleNonNegativeCoordinates z w
      0≤re-z 0≤im-z 0≤re-w 0≤im-w

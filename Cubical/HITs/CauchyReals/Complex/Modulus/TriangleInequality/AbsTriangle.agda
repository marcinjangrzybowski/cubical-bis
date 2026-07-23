module Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality.AbsTriangle where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Triangle
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality.NonNegativeComplex


opaque
  absNonNegative : ∀ x → 0 ≤ᵣ absᵣ x
  absNonNegative x = 0≤absᵣ x


absoluteFirstQuadrant : ℂ → FirstQuadrantℂ
absoluteFirstQuadrant z =
  absComplex z , absNonNegative (re z) , absNonNegative (im z)


opaque
  absoluteTriangleRaw : ∀ z w →
    modulus
      (fst (absoluteFirstQuadrant z) +ℂ fst (absoluteFirstQuadrant w)) ≤ᵣ
    modulus (fst (absoluteFirstQuadrant z)) +ᵣ
      modulus (fst (absoluteFirstQuadrant w))
  absoluteTriangleRaw z w =
    firstQuadrantTriangle (absoluteFirstQuadrant z) (absoluteFirstQuadrant w)


opaque
  absoluteUnderlying : ∀ z →
    fst (absoluteFirstQuadrant z) ≡ absComplex z
  absoluteUnderlying _ = refl


opaque
  absoluteTriangleLeftPath : ∀ z w →
    modulus
      (fst (absoluteFirstQuadrant z) +ℂ fst (absoluteFirstQuadrant w)) ≡
    modulus (absComplex z +ℂ absComplex w)
  absoluteTriangleLeftPath z w = cong modulus
    (cong₂ _+ℂ_ (absoluteUnderlying z) (absoluteUnderlying w))


opaque
  absoluteTriangleRightPath : ∀ z w →
    modulus (fst (absoluteFirstQuadrant z)) +ᵣ
      modulus (fst (absoluteFirstQuadrant w)) ≡
    modulus (absComplex z) +ᵣ modulus (absComplex w)
  absoluteTriangleRightPath z w = cong₂ _+ᵣ_
    (cong modulus (absoluteUnderlying z))
    (cong modulus (absoluteUnderlying w))


opaque
  modulusAbsTriangle : ∀ z w →
    modulus (absComplex z +ℂ absComplex w) ≤ᵣ
    modulus (absComplex z) +ᵣ modulus (absComplex w)
  modulusAbsTriangle z w = subst2 _≤ᵣ_
    (absoluteTriangleLeftPath z w)
    (absoluteTriangleRightPath z w)
    (absoluteTriangleRaw z w)

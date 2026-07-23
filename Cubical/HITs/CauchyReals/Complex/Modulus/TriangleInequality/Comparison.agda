module Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality.Comparison where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Triangle
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality.AbsoluteSums


opaque
  modulusAdd≤absAdd : ∀ z w →
    modulus (z +ℂ w) ≤ᵣ modulus (absComplex z +ℂ absComplex w)
  modulusAdd≤absAdd (a , b) (c , d) =
    modulusMonotoneAbsCoords ((a , b) +ℂ (c , d))
      (absComplex (a , b) +ℂ absComplex (c , d))
      (absSumBound a c) (absSumBound b d)

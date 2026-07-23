module Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality.Core where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Triangle
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality.AbsoluteSums public
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality.Comparison public
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality.NonNegative public


opaque
  modulusAbsTriangleFinal : ∀ z w →
    modulus (absComplex z +ℂ absComplex w) ≤ᵣ
    modulus z +ᵣ modulus w
  modulusAbsTriangleFinal z w = isTrans≤≡ᵣ _ _ _
    (modulusAbsTriangle z w) (modulusAbsPath z w)


opaque
  modulus-triangle : ∀ z w →
    modulus (z +ℂ w) ≤ᵣ modulus z +ᵣ modulus w
  modulus-triangle z w = isTrans≤ᵣ _ _ _
    (modulusAdd≤absAdd z w)
    (modulusAbsTriangleFinal z w)

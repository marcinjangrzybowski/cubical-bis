module Cubical.HITs.CauchyReals.Complex.Metric.Coordinates.UpperBound where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


opaque
  complex-from-coordinates : ∀ z →
    z ≡ fromℝ (re z) +ℂ imagℂ (im z)
  complex-from-coordinates _ = ℂ≡ ℝ! ℝ!


opaque
  modulus≤abs-coordinates : ∀ z →
    modulus z ≤ᵣ absᵣ (re z) +ᵣ absᵣ (im z)
  modulus≤abs-coordinates z = isTrans≡≤ᵣ _ _ _
    (cong modulus (complex-from-coordinates z))
    (isTrans≤≡ᵣ _ _ _
      (modulus-triangle (fromℝ (re z)) (imagℂ (im z)))
      (cong₂ _+ᵣ_ (modulus-fromℝ (re z)) (modulus-imag (im z))))

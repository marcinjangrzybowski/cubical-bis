module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.FiniteSum.Distance where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Ring

open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Base
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.Base
open import
  Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.FiniteSum.Ordered


private
  swap-partialSum-distance-bound :
    (terms : ComplexSequence) → (m n : ℕ) →
    modulus
      (partialSumℂ terms m -ℂ partialSumℂ terms n) ≤ᵣ
    absᵣ
      (absolutePartialSum terms m -ᵣ
       absolutePartialSum terms n) →
    modulus
      (partialSumℂ terms n -ℂ partialSumℂ terms m) ≤ᵣ
    absᵣ
      (absolutePartialSum terms n -ᵣ
       absolutePartialSum terms m)
  swap-partialSum-distance-bound terms m n =
    subst2 _≤ᵣ_
      (modulus-difference-sym
        (partialSumℂ terms m)
        (partialSumℂ terms n))
      (minusComm-absᵣ
        (absolutePartialSum terms m)
        (absolutePartialSum terms n))


opaque
  partialSum-distance-bound :
    (terms : ComplexSequence) → (m n : ℕ) →
    modulus
      (partialSumℂ terms m -ℂ partialSumℂ terms n) ≤ᵣ
    absᵣ
      (absolutePartialSum terms m -ᵣ
       absolutePartialSum terms n)
  partialSum-distance-bound terms =
    ℕ.elimBy≤
      (swap-partialSum-distance-bound terms)
      λ m n m≤n →
        swap-partialSum-distance-bound terms n m
          (ordered-partialSum-distance-bound terms m n m≤n)

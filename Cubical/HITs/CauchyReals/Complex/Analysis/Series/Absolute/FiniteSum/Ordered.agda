module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.FiniteSum.Ordered where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Strict
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using
  (seriesDiff)

open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Base
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.Base
open import
  Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.FiniteSum.Bound
open import
  Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.FiniteSum.Shift


opaque
  ordered-partialSum-distance-bound :
    (terms : ComplexSequence) → (m n : ℕ) → m ℕ.≤ n →
    modulus
      (partialSumℂ terms n -ℂ partialSumℂ terms m) ≤ᵣ
    absᵣ
      (absolutePartialSum terms n -ᵣ
       absolutePartialSum terms m)
  ordered-partialSum-distance-bound terms m n m≤n =
    let
      count = n ℕ.∸ m
      count+m≡n = ℕ.[n-m]+m m n m≤n

      complexDifference :
        partialSumℂ terms n -ℂ partialSumℂ terms m ≡
        partialSumℂ (λ k → terms (k ℕ.+ m)) count
      complexDifference =
        cong
          (λ k →
            partialSumℂ terms k -ℂ partialSumℂ terms m)
          (sym count+m≡n)
        ∙ partialSum-shift-difference terms m count

      realDifference :
        absolutePartialSum
          (λ k → terms (k ℕ.+ m)) count ≡
        absolutePartialSum terms n -ᵣ
          absolutePartialSum terms m
      realDifference =
        sym
          (seriesDiff
            (λ k → modulus (terms k)) m count)
        ∙ cong
          (λ k →
            absolutePartialSum terms k -ᵣ
            absolutePartialSum terms m)
          count+m≡n
    in
    isTrans≤ᵣ _ _ _
      (isTrans≤≡ᵣ _ _ _
        (isTrans≡≤ᵣ _ _ _
          (cong modulus complexDifference)
          (modulus-partialSum≤partialSum-modulus
            (λ k → terms (k ℕ.+ m)) count))
        realDifference)
      (≤absᵣ
        (absolutePartialSum terms n -ᵣ
         absolutePartialSum terms m))

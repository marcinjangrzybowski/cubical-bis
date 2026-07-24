module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.FiniteSum.Bound where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using (seqΣ)

open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Zero
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Base
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.Base


private
  partialSumBoundZero : modulus 0ℂ ≤ᵣ 0
  partialSumBoundZero = ≡ᵣWeaken≤ᵣ _ _ modulus0


  partialSumBoundStep : (terms : ComplexSequence) → (n : ℕ) →
    modulus (partialSumℂ terms n) ≤ᵣ
      seqΣ (λ k → modulus (terms k)) n →
    modulus (partialSumℂ terms n +ℂ terms n) ≤ᵣ
      seqΣ (λ k → modulus (terms k)) n +ᵣ modulus (terms n)
  partialSumBoundStep terms n previous =
    isTrans≤ᵣ _ _ _
      (modulus-triangle (partialSumℂ terms n) (terms n))
      (≤ᵣ-+o _ _ _ previous)


  partialSumZero : (terms : ComplexSequence) →
    partialSumℂ terms zero ≡ 0ℂ
  partialSumZero terms = refl


  absolutePartialSumZero : (terms : ComplexSequence) →
    seqΣ (λ k → modulus (terms k)) zero ≡ 0
  absolutePartialSumZero terms = refl


  partialSumStep : (terms : ComplexSequence) → (n : ℕ) →
    partialSumℂ terms (suc n) ≡
    partialSumℂ terms n +ℂ terms n
  partialSumStep terms n = refl


  absolutePartialSumStep : (terms : ComplexSequence) → (n : ℕ) →
    seqΣ (λ k → modulus (terms k)) (suc n) ≡
    seqΣ (λ k → modulus (terms k)) n +ᵣ modulus (terms n)
  absolutePartialSumStep terms n = refl


modulus-partialSum≤partialSum-modulus :
  (terms : ComplexSequence) → (n : ℕ) →
  modulus (partialSumℂ terms n) ≤ᵣ
  seqΣ (λ k → modulus (terms k)) n
modulus-partialSum≤partialSum-modulus terms zero =
  subst2 _≤ᵣ_
    (cong modulus (sym (partialSumZero terms)))
    (sym (absolutePartialSumZero terms))
    partialSumBoundZero
modulus-partialSum≤partialSum-modulus terms (suc n) =
  subst2 _≤ᵣ_
    (cong modulus (sym (partialSumStep terms n)))
    (sym (absolutePartialSumStep terms n))
    (partialSumBoundStep terms n
      (modulus-partialSum≤partialSum-modulus terms n))

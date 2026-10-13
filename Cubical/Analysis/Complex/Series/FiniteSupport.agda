module Cubical.Analysis.Complex.Series.FiniteSupport where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as Nat
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Analysis.Real.Sequence as Real
import Cubical.Analysis.Real.Sequence.Eventually as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base

-- Explicit finite support determines the sum at its cutoff.
opaque
  finiteSupportPartialSumℂStable : ∀ terms cutoff →
    (∀ n → cutoff Nat.≤ n → terms n ≡ 0ℂ) →
    ∀ n → cutoff Nat.≤ n → partialSumℂ terms n ≡ partialSumℂ terms cutoff
  finiteSupportPartialSumℂStable terms cutoff vanishes n (difference , equal) =
    subst (λ index → partialSumℂ terms index ≡ partialSumℂ terms cutoff) equal (go difference)
    where
    go : ∀ count → partialSumℂ terms (count Nat.+ cutoff) ≡ partialSumℂ terms cutoff
    go zero = refl
    go (suc count) = cong₂ _+ℂ_ (go count) (vanishes (count Nat.+ cutoff) (Nat.≤SumRight {n = cutoff} {k = count}))
      ∙ +ℂIdR (partialSumℂ terms cutoff)

  finiteSupportHasComplexSum : ∀ terms cutoff →
    (∀ n → cutoff Nat.≤ n → terms n ≡ 0ℂ) → HasComplexSum terms (partialSumℂ terms cutoff)
  finiteSupportHasComplexSum terms cutoff vanishes =
    Real.eventuallyEqualPresIsLimitSequence
      {x = λ _ → re (partialSumℂ terms cutoff)} {y = re ∘ partialSumℂ terms}
      {l = re (partialSumℂ terms cutoff)}
      ∣ cutoff , (λ n late → cong re (sym (finiteSupportPartialSumℂStable terms cutoff vanishes n late))) ∣₁
      (Real.constantIsLimitSequence (re (partialSumℂ terms cutoff))) ,
    Real.eventuallyEqualPresIsLimitSequence
      {x = λ _ → im (partialSumℂ terms cutoff)} {y = im ∘ partialSumℂ terms}
      {l = im (partialSumℂ terms cutoff)}
      ∣ cutoff , (λ n late → cong im (sym (finiteSupportPartialSumℂStable terms cutoff vanishes n late))) ∣₁
      (Real.constantIsLimitSequence (im (partialSumℂ terms cutoff)))

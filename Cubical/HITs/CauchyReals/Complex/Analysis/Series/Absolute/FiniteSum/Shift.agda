module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.FiniteSum.Shift where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ

open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Base


opaque
  partialSum-shift-difference :
    (terms : ComplexSequence) → (start count : ℕ) →
    partialSumℂ terms (count ℕ.+ start) -ℂ
      partialSumℂ terms start ≡
    partialSumℂ (λ k → terms (k ℕ.+ start)) count
  partialSum-shift-difference terms start zero =
    +ℂInvR (partialSumℂ terms start)
  partialSum-shift-difference terms start (suc count) =
    cong (_+ℂ _) (+ℂComm _ _)
    ∙∙ sym (+ℂAssoc _ _ _)
    ∙∙ cong (terms (count ℕ.+ start) +ℂ_)
      (partialSum-shift-difference terms start count)
    ∙ +ℂComm
      (terms (count ℕ.+ start))
      (partialSumℂ (λ k → terms (k ℕ.+ start)) count)

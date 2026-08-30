module Cubical.Analysis.Real.FiniteSum.Reindexing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc; _∸_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Series.Base


-- Decompose an initial-segment sum at its first rather than its last term.
partialSum-first : ∀ terms n →
  partialSum terms (suc n) ≡
  terms zero + partialSum (terms ∘ suc) n
partialSum-first terms zero =
  addIdL (terms zero)
  ∙ sym (addIdR (terms zero))
partialSum-first terms (suc n) =
  cong (_+ terms (suc n))
    (partialSum-first terms n)
  ∙ sym
      (addAssoc
        (terms zero)
        (partialSum (terms ∘ suc) n)
        (terms (suc n)))


boundedSubtractInvolutive :
  ∀ k n → k ℕ.≤ n →
  k ≡ n ∸ (n ∸ k)
boundedSubtractInvolutive k n k≤n =
  ℕ.inj-+m
    ( ℕ.+-comm k (n ∸ k)
    ∙ ℕ.[n-m]+m k n k≤n
    ∙ sym
        (ℕ.[n-m]+m
          (n ∸ k) n
          (ℕ.∸-≤ n k))
    )


-- Reversal of the finite interval [0,n].  This is the reindexing used to
-- exchange the two factors in an anti-diagonal convolution sum.
partialSum-reverse : ∀ terms n →
  partialSum terms (suc n) ≡
  partialSum (λ k → terms (n ∸ k)) (suc n)
partialSum-reverse terms zero = refl
partialSum-reverse terms (suc n) =
  cong (_+ terms (suc n))
    (partialSum-reverse terms n)
  ∙ addComm
      (partialSum (λ k → terms (n ∸ k)) (suc n))
      (terms (suc n))
  ∙ sym
      (partialSum-first
        (λ k → terms (suc n ∸ k))
        (suc n))


-- The n-th anti-diagonal of a doubly indexed family.
diagonalSum : (ℕ → ℕ → ℝ) → ℕ → ℝ
diagonalSum terms n =
  partialSum (λ k → terms k (n ∸ k)) (suc n)


diagonalSum-zero : ∀ terms →
  diagonalSum terms zero ≡ terms zero zero
diagonalSum-zero terms =
  addIdL (terms zero zero)


diagonalSum-first : ∀ terms n →
  diagonalSum terms (suc n) ≡
  terms zero (suc n)
    + diagonalSum (λ i j → terms (suc i) j) n
diagonalSum-first terms n =
  partialSum-first
    (λ k → terms k (suc n ∸ k))
    (suc n)


-- The lower triangular region i+j<n, represented as rows.  Keeping this
-- independent of multiplication lets convolution, absolute convolution,
-- and coefficient products share the same reindexing proof.
triangularSum : (ℕ → ℕ → ℝ) → ℕ → ℝ
triangularSum terms n =
  partialSum
    (λ i → partialSum (terms i) (n ∸ i))
    n


triangularSum-first : ∀ terms n →
  triangularSum terms (suc n) ≡
  partialSum (terms zero) (suc n)
    + triangularSum (λ i j → terms (suc i) j) n
triangularSum-first terms n =
  partialSum-first
    (λ i → partialSum (terms i) (suc n ∸ i))
    n


-- Enlarging a lower triangle by one layer adds exactly its new diagonal.
triangularSum-step : ∀ terms n →
  triangularSum terms (suc n) ≡
  triangularSum terms n + diagonalSum terms n
triangularSum-step terms zero = refl
triangularSum-step terms (suc n) =
  triangularSum-first terms (suc n)
  ∙ cong
      (partialSum (terms zero) (suc (suc n)) +_)
      (triangularSum-step shiftedTerms n)
  ∙ interchange
  ∙ cong₂ _+_
      (sym (triangularSum-first terms n))
      (sym (diagonalSum-first terms n))
  where
  shiftedTerms : ℕ → ℕ → ℝ
  shiftedTerms i j = terms (suc i) j

  interchange :
    (partialSum (terms zero) (suc n) + terms zero (suc n))
      + (triangularSum shiftedTerms n
        + diagonalSum shiftedTerms n)
      ≡
    (partialSum (terms zero) (suc n)
      + triangularSum shiftedTerms n)
      + (terms zero (suc n)
        + diagonalSum shiftedTerms n)
  interchange =
    sym
      (addAssoc
        (partialSum (terms zero) (suc n))
        (terms zero (suc n))
        (triangularSum shiftedTerms n
          + diagonalSum shiftedTerms n))
    ∙ cong (partialSum (terms zero) (suc n) +_)
        ( addAssoc
            (terms zero (suc n))
            (triangularSum shiftedTerms n)
            (diagonalSum shiftedTerms n)
        ∙ cong (_+ diagonalSum shiftedTerms n)
            (addComm
              (terms zero (suc n))
              (triangularSum shiftedTerms n))
        ∙ sym
            (addAssoc
              (triangularSum shiftedTerms n)
              (terms zero (suc n))
              (diagonalSum shiftedTerms n))
        )
    ∙ addAssoc
        (partialSum (terms zero) (suc n))
        (triangularSum shiftedTerms n)
        (terms zero (suc n)
          + diagonalSum shiftedTerms n)


-- Summing the first n diagonals is the same as summing the corresponding
-- triangular region row by row.
partialSum-diagonalSum : ∀ terms n →
  partialSum (diagonalSum terms) n ≡
  triangularSum terms n
partialSum-diagonalSum terms zero = refl
partialSum-diagonalSum terms (suc n) =
  cong (_+ diagonalSum terms n)
    (partialSum-diagonalSum terms n)
  ∙ sym (triangularSum-step terms n)

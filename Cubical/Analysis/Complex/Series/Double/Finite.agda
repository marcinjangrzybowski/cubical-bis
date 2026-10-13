module Cubical.Analysis.Complex.Series.Double.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; suc; _∸_)
import Cubical.Analysis.Real.FiniteSum.Reindexing as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Series.Base

-- These are the coordinatewise native real diagonal and triangular sums.
-- In particular the index region is i + j < count, with no infinite
-- reindexing or convergence assertion hidden in these definitions.
diagonalSumℂ : (ℕ → ℕ → ℂ) → ℕ → ℂ
diagonalSumℂ terms n = partialSumℂ (λ k → terms k (n ∸ k)) (suc n)

triangularSumℂ : (ℕ → ℕ → ℂ) → ℕ → ℂ
triangularSumℂ terms n = partialSumℂ (λ k → partialSumℂ (terms k) (n ∸ k)) n

partialSumℂ-diagonalSum : ∀ terms n → partialSumℂ (diagonalSumℂ terms) n ≡ triangularSumℂ terms n
partialSumℂ-diagonalSum terms n = ℂ≡
  (Real.partialSum-diagonalSum (λ i j → re (terms i j)) n)
  (Real.partialSum-diagonalSum (λ i j → im (terms i j)) n)

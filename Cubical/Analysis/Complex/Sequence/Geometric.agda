module Cubical.Analysis.Complex.Sequence.Geometric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (suc)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Sequence.Geometric
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence

-- The same explicit geometric tail estimate feeds both native real limits.
geometricComplexIncrementsCauchy : (z : ComplexSequence) (q coefficient : ℝ) →
  0ℝ ≤ℝ q → q <ℝ 1ℝ →
  (∀ n → normℂ (z (suc n) -ℂ z n) ≤ℝ coefficient · powℝ q n) →
  ComplexSeqWitness z
geometricComplexIncrementsCauchy z q coefficient nonnegative below bounds =
  geometricallyBoundedIncrementsCauchy (re ∘ z) q coefficient nonnegative below
    (λ n → ≤ℝ-trans (absℝ (re (z (suc n) -ℂ z n)))
      (normℂ (z (suc n) -ℂ z n)) (coefficient · powℝ q n)
      (reAbs≤normℂ (z (suc n) -ℂ z n)) (bounds n)) ,
  geometricallyBoundedIncrementsCauchy (im ∘ z) q coefficient nonnegative below
    (λ n → ≤ℝ-trans (absℝ (im (z (suc n) -ℂ z n)))
      (normℂ (z (suc n) -ℂ z n)) (coefficient · powℝ q n)
      (imAbs≤normℂ (z (suc n) -ℂ z n)) (bounds n))

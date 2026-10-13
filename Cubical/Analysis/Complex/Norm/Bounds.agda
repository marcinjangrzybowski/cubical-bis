module Cubical.Analysis.Complex.Norm.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm

normℂ-addBound : ∀ z w a b → normℂ z ≤ℝ a → normℂ w ≤ℝ b →
  normℂ (z +ℂ w) ≤ℝ a + b
normℂ-addBound z w a b za wb = ≤ℝ-trans
  (normℂ (z +ℂ w)) (normℂ z + normℂ w) (a + b)
  (normℂ-triangle z w) (addPres≤ (normℂ z) a (normℂ w) b za wb)

normℂ-mulBound : ∀ z w a b → normℂ z ≤ℝ a → normℂ w ≤ℝ b →
  normℂ (z ·ℂ w) ≤ℝ a · b
normℂ-mulBound z w a b za wb = ≤ℝ-trans
  (normℂ (z ·ℂ w)) (normℂ z · normℂ w) (a · b)
  (normℂ-submultiplicative z w)
  (mulPres≤ (normℂ z) a (normℂ w) b
    (≤ℝ-trans 0ℝ (normℂ z) a (normℂ-nonnegative z) za)
    (normℂ-nonnegative w) za wb)

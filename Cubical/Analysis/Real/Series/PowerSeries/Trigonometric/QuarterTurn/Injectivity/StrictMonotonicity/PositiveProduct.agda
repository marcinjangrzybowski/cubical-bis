module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.PositiveProduct where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ; addIdL)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication


opaque
  positiveProductTwice : ∀ (left right : ℝ) →
    0ℝ <ℝ left → 0ℝ <ℝ right →
    0ℝ <ℝ (left · right) + (left · right)
  positiveProductTwice left right positive-left positive-right =
    subst (_<ℝ product + product)
      (addIdL 0ℝ)
      (<ℝ-add 0ℝ product 0ℝ product
        positive-product positive-product)
    where
    product : ℝ
    product = left · right

    positive-product : 0ℝ <ℝ product
    positive-product =
      mulPositive left right positive-left positive-right

module Cubical.Analysis.Real.Functions.Exponential where

open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Order


-- The elementary function is the existing globally convergent power series.
expℝ : ℝ → ℝ
expℝ = exponentialEntireValue

expℝ-positive : ∀ x → 0ℝ <ℝ expℝ x
expℝ-positive = exponentialEntireValue-positive

opaque
  expPositive : ℝ → ℝ>0
  expPositive x = expℝ x , expℝ-positive x

  expPositive-value : ∀ x → fst (expPositive x) ≡ expℝ x
  expPositive-value x = refl

  expPositive-isEmbedding : isEmbedding expPositive
  expPositive-isEmbedding = injEmbedding isSetℝ>0
    (λ {x} {y} equal → exponentialEntireValue-injective x y (cong fst equal))

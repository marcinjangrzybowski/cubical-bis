module Cubical.Analysis.Real.Functions.Logarithm.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Positive using (ℝ>0)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Functions.Logarithm.Global
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Continuity.Reflection
open import Cubical.Analysis.Real.Integration.UniformContinuity

-- The existing exponential reflection estimate gives uniform continuity of
-- the native logarithm on every positive half-line. No upper bound is needed.
logℝUniformAlongAbove : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
  (f : A → ℝ>0) (lower : ℝ>0) → (∀ x → fst lower ≤ℝ fst (f x)) →
  IsRadiuswiseUniformlyContinuous source (fst ∘ f) (ℝPremetricSpace .snd) →
  IsRadiuswiseUniformlyContinuous source (logℝ ∘ f) (ℝPremetricSpace .snd)
logℝUniformAlongAbove source f lower bounded continuous ε = do
  (ρ , reflects) ← exponentialEntireValueClosenessReflectionAbove (logℝ lower) ε
  (δ , near) ← continuous ρ
  return (δ , λ x y close → reflects (logℝ (f x)) (logℝ (f y))
    (logℝ-preserves≤ lower (f x) (bounded x)) (logℝ-preserves≤ lower (f y) (bounded y))
    (subst2 (_∼[ ρ ]_) (sym (expℝ-logℝ (f x))) (sym (expℝ-logℝ (f y))) (near x y close)))

module Cubical.Analysis.Real.Functions.Exponential.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Bounds.Range
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Functions.Exponential.InverseIteration


-- The sequence itself is determined by arithmetic. Its Cauchy witness comes
-- from geometric domination, not from choosing approximate solutions.
opaque
  exponentialBracketedPreimage : ∀ a b target → a ≤ℝ b →
    expℝ a ≤ℝ target → target ≤ℝ expℝ b →
    Σ[ x ∈ ℝ ] expℝ x ≡ target
  exponentialBracketedPreimage a b target ordered lower upper =
    DampedIteration.value a b target ordered lower upper
    , DampedIteration.value-preimage a b target ordered lower upper

  exponentialPositivePreimage : (target : ℝ>0) →
    Σ[ x ∈ ℝ ] expℝ x ≡ fst target
  exponentialPositivePreimage (target , positive) =
    let (a , b , ordered , lower , upper) =
          exponentialPositiveTargetBracket target positive
    in exponentialBracketedPreimage a b target
      (<ℝ-weaken a b ordered)
      (<ℝ-weaken (expℝ a) target lower)
      (<ℝ-weaken target (expℝ b) upper)

  expPositive-isSurjection : isSurjection expPositive
  expPositive-isSurjection target =
    let (x , equation) = exponentialPositivePreimage target
    in ∣ x , Σ≡Prop (isProp<ℝ 0ℝ) (expPositive-value x ∙ equation) ∣₁

  expPositive-isEquiv : isEquiv expPositive
  expPositive-isEquiv =
    isEmbedding×isSurjection→isEquiv
      (expPositive-isEmbedding , expPositive-isSurjection)


expPositiveEquiv : ℝ ≃ ℝ>0
expPositiveEquiv = expPositive , expPositive-isEquiv

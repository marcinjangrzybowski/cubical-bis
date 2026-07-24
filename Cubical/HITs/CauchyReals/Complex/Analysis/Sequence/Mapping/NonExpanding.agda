module Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Mapping.NonExpanding where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence


mapConvergesPres≈ :
  (f : ℂ → ℂ) →
  ((z w : ℂ) (ε : ℚ₊) → z ≈ℂ[ ε ] w → f z ≈ℂ[ ε ] f w) →
  (sequence : ComplexSequence) → (limit : ℂ) →
  ConvergesToℂ sequence limit →
  ConvergesToℂ (λ n → f (sequence n)) (f limit)
mapConvergesPres≈ f f-pres≈ sequence limit (N , converges) =
  N , λ ε n N≤n →
    f-pres≈ (sequence n) limit ε
      (converges ε n N≤n)


mapCauchyPres≈ :
  (f : ℂ → ℂ) →
  ((z w : ℂ) (ε : ℚ₊) → z ≈ℂ[ ε ] w → f z ≈ℂ[ ε ] f w) →
  (sequence : ComplexSequence) →
  IsCauchySequenceℂ sequence →
  IsCauchySequenceℂ (λ n → f (sequence n))
mapCauchyPres≈ f f-pres≈ sequence (N , cauchy) =
  N , λ ε m n N≤m N≤n →
    f-pres≈ (sequence m) (sequence n) ε
      (cauchy ε m n N≤m N≤n)

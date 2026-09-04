module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Choice where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

import Cubical.Axiom.Choice as AC

open import Cubical.Relation.Premetric.Instances.Rationals
import Cubical.Relation.Premetric.Completion.Comparison
  as CompletionComparisonDefinition

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Sequence


module RationalCompletionComparison =
  CompletionComparisonDefinition ℚPremetricSpace

open PositiveRationals using (ℚ₊; ℚ₊≡)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open 1/2∈ℚ using (/2+/2≡id)


-- Countable choice in precisely the form needed below.  This is an
-- explicit hypothesis, not an axiom assumed by the trigonometry library.

PositiveRationalChoice₀ : Type₁
PositiveRationalChoice₀ =
  RationalCompletionComparison.PositiveRationalChoice ℓ-zero


-- Sequential convergence contains a merely existing tail at each radius.
-- Positive-rational choice is exactly what is needed to assemble those tails
-- into the single modulus stored by `SeqWitness`.

isLimitSequence→radiuswiseCauchy :
  ∀ {sequence : ℕ → ℝ} {limit : ℝ} →
  isLimitSequence sequence limit →
  RationalCompletionComparison.MiddleWitnesses.RadiuswiseCauchySequence
    sequence
isLimitSequence→radiuswiseCauchy {sequence} {limit} converges input =
  PT.map to-cauchy-tail (converges (input /2₊))
  where
  to-cauchy-tail :
    Σ[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n → sequence n ∼[ input /2₊ ] limit) →
    RationalCompletionComparison.MiddleWitnesses.CauchyTail
      sequence input
  to-cauchy-tail (N , close) =
    N
    , λ m n N≤m N≤n →
        subst (sequence m ∼[_] sequence n)
          (ℚ₊≡ (/2+/2≡id (fst input)))
          (triangle∼
            (sequence m) limit (sequence n)
            (input /2₊) (input /2₊)
            (close m N≤m)
            (sym∼ (sequence n) limit (input /2₊) (close n N≤n)))


positiveRationalChoice→convergentSeqWitness :
  PositiveRationalChoice₀ →
  ∀ {sequence : ℕ → ℝ} {limit : ℝ} →
  isLimitSequence sequence limit →
  SeqWitness sequence
positiveRationalChoice→convergentSeqWitness
    choice {sequence} converges =
  RationalCompletionComparison.positiveRationalChoice→sequentialTailChoice
    choice sequence (isLimitSequence→radiuswiseCauchy converges)


positiveRationalChoice→mereChosenSineClosenessReflectionModulus :
  ∀ quarter →
  PositiveRationalChoice₀ →
  QuarterTurnSineClosenessReflectionModulus quarter →
  MereChosenQuarterTurnSineClosenessReflectionModulus quarter
positiveRationalChoice→mereChosenSineClosenessReflectionModulus
    quarter choice pointwise =
  choice
    (λ input →
      Σ[ output ∈ ℚ₊ ]
        QuarterTurnSineClosenessReflection quarter input output)
    pointwise


propositionalChoice→mereChosenSineClosenessReflectionModulus :
  ∀ quarter →
  AC.satAC ℓ-zero 1 ℚ₊ →
  QuarterTurnSineClosenessReflectionModulus quarter →
  MereChosenQuarterTurnSineClosenessReflectionModulus quarter
propositionalChoice→mereChosenSineClosenessReflectionModulus
    quarter choice =
  positiveRationalChoice→mereChosenSineClosenessReflectionModulus
    quarter
    (RationalCompletionComparison.propositionalChoice→positiveRationalChoice
      choice)

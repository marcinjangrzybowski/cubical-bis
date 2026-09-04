module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Sequence.Chosen where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Sequence.Transfer


opaque
  quarterSineChosenClosenessReflection : ∀ quarter →
    (modulus : ChosenQuarterTurnSineClosenessReflectionModulus quarter) →
    (points : ℕ → SineQuarterInterval quarter) →
    ChosenClosenessReflection
      (λ n → fst (points n))
      (λ n → sinℝ (fst (points n)))
  quarterSineChosenClosenessReflection
      quarter modulus points input =
    fst (modulus input)
    , λ m n image-close →
        snd (modulus input) (points m) (points n) image-close


  chosenSineClosenessReflection-presCauchySeq : ∀ quarter →
    (modulus : ChosenQuarterTurnSineClosenessReflectionModulus quarter) →
    (points : ℕ → SineQuarterInterval quarter) →
    CauchySeq (λ n → sinℝ (fst (points n))) →
    CauchySeq (λ n → fst (points n))
  chosenSineClosenessReflection-presCauchySeq
      quarter modulus points =
    chosenClosenessReflection-presCauchySeq
      (λ n → fst (points n))
      (λ n → sinℝ (fst (points n)))
      (quarterSineChosenClosenessReflection quarter modulus points)


  chosenSineClosenessReflection-presSeqWitness : ∀ quarter →
    ChosenQuarterTurnSineClosenessReflectionModulus quarter →
    (points : ℕ → SineQuarterInterval quarter) →
    SeqWitness (λ n → sinℝ (fst (points n))) →
    SeqWitness (λ n → fst (points n))
  chosenSineClosenessReflection-presSeqWitness
      quarter modulus points =
    chosenClosenessReflection-presSeqWitness
      (λ n → fst (points n))
      (λ n → sinℝ (fst (points n)))
      (quarterSineChosenClosenessReflection quarter modulus points)

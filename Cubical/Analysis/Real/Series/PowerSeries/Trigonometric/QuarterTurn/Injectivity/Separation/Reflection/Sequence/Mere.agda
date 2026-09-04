module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Sequence.Mere where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Sequence.Chosen


opaque
  mereChosenSineClosenessReflection-presSeqWitness : ∀ quarter →
    MereChosenQuarterTurnSineClosenessReflectionModulus quarter →
    (points : ℕ → SineQuarterInterval quarter) →
    SeqWitness (λ n → sinℝ (fst (points n))) →
    SeqWitness (λ n → fst (points n))
  mereChosenSineClosenessReflection-presSeqWitness
      quarter mere-modulus points image-witness =
    PT.rec squash₁
      (λ modulus →
        chosenSineClosenessReflection-presSeqWitness
          quarter modulus points image-witness)
      mere-modulus

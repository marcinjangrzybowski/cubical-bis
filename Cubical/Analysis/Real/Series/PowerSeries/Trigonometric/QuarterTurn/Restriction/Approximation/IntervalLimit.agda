module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.IntervalLimit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base


sineQuarterSequenceLimit : ∀ quarter →
  (points : ℕ → SineQuarterInterval quarter) →
  SeqWitness (λ n → fst (points n)) → ℝ
sineQuarterSequenceLimit quarter points points-cauchy =
  lim (λ n → fst (points n)) points-cauchy


opaque
  sineQuarterSequenceLimit-converges : ∀ quarter →
    (points : ℕ → SineQuarterInterval quarter) →
    (points-cauchy : SeqWitness (λ n → fst (points n))) →
    isLimitSequence (λ n → fst (points n))
      (sineQuarterSequenceLimit quarter points points-cauchy)
  sineQuarterSequenceLimit-converges quarter points points-cauchy =
    lim-isLimitSeq (λ n → fst (points n)) points-cauchy


opaque
  sineQuarterSequenceLimit-lower : ∀ quarter →
    (points : ℕ → SineQuarterInterval quarter) →
    (points-cauchy : SeqWitness (λ n → fst (points n))) →
    (- quarter) ≤ℝ
      sineQuarterSequenceLimit quarter points points-cauchy
  sineQuarterSequenceLimit-lower quarter points points-cauchy =
    pointwiseLePresLimits
      (λ n → fst (snd (points n)))
      (constantIsLimitSequence (- quarter))
      (lim-isLimitSeq (λ n → fst (points n)) points-cauchy)


  sineQuarterSequenceLimit-upper : ∀ quarter →
    (points : ℕ → SineQuarterInterval quarter) →
    (points-cauchy : SeqWitness (λ n → fst (points n))) →
    sineQuarterSequenceLimit quarter points points-cauchy
      ≤ℝ quarter
  sineQuarterSequenceLimit-upper quarter points points-cauchy =
    pointwiseLePresLimits
      (λ n → snd (snd (points n)))
      (lim-isLimitSeq (λ n → fst (points n)) points-cauchy)
      (constantIsLimitSequence quarter)


sineQuarterSequenceLimitPoint : ∀ quarter →
  (points : ℕ → SineQuarterInterval quarter) →
  (points-cauchy : SeqWitness (λ n → fst (points n))) →
  SineQuarterInterval quarter
sineQuarterSequenceLimitPoint quarter points points-cauchy =
  sineQuarterSequenceLimit quarter points points-cauchy
  , sineQuarterSequenceLimit-lower quarter points points-cauchy
  , sineQuarterSequenceLimit-upper quarter points points-cauchy


sineQuarterSequenceLimitPoint-value : ∀ quarter →
  (points : ℕ → SineQuarterInterval quarter) →
  (points-cauchy : SeqWitness (λ n → fst (points n))) →
  fst (sineQuarterSequenceLimitPoint quarter points points-cauchy)
    ≡ sineQuarterSequenceLimit quarter points points-cauchy
sineQuarterSequenceLimitPoint-value quarter points points-cauchy = refl


sineQuarterSequenceLimitPointWith : ∀ {ℓ} quarter →
  (points : ℕ → SineQuarterInterval quarter) →
  (points-cauchy : SeqWitness (λ n → fst (points n))) →
  (P : ℝ → Type ℓ) →
  P (sineQuarterSequenceLimit quarter points points-cauchy) →
  Σ[ point ∈ SineQuarterInterval quarter ] P (fst point)
sineQuarterSequenceLimitPointWith
    quarter points points-cauchy P property =
  ( sineQuarterSequenceLimit quarter points points-cauchy
  , sineQuarterSequenceLimit-lower quarter points points-cauchy
  , sineQuarterSequenceLimit-upper quarter points points-cauchy
  )
  , property

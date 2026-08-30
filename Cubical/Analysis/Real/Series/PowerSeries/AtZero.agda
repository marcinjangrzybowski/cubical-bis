module Cubical.Analysis.Real.Series.PowerSeries.AtZero where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


zeroPowSuc : ∀ n → powℝ 0ℝ (suc n) ≡ 0ℝ
zeroPowSuc n =
  ℝRing.0LeftAnnihilates (powℝ 0ℝ n)


powerSeriesPositiveTermAtZero : ∀ coefficients n →
  powerSeriesTerms coefficients 0ℝ (suc n) ≡ 0ℝ
powerSeriesPositiveTermAtZero coefficients n =
  cong (coefficients (suc n) ·_) (zeroPowSuc n)
  ∙ ℝRing.0RightAnnihilates (coefficients (suc n))


powerSeriesPartialSumAtZero : ∀ coefficients n →
  partialSum (powerSeriesTerms coefficients 0ℝ) (suc n)
    ≡ coefficients zero
powerSeriesPartialSumAtZero coefficients zero =
  addIdL (powerSeriesTerms coefficients 0ℝ zero)
  ∙ powerSeriesTerms-zero coefficients
powerSeriesPartialSumAtZero coefficients (suc n) =
  cong₂ _+_
    (powerSeriesPartialSumAtZero coefficients n)
    (powerSeriesPositiveTermAtZero coefficients n)
  ∙ addIdR (coefficients zero)


powerSeriesAtZeroHasSum : ∀ coefficients →
  HasSum
    (powerSeriesTerms coefficients 0ℝ)
    (coefficients zero)
powerSeriesAtZeroHasSum coefficients =
  eventuallyEqualPresIsLimitSequence
    ∣ suc zero
    , (λ where
        zero impossible →
          ⊥.rec (ℕ.¬-<-zero impossible)
        (suc n) _ →
          sym (powerSeriesPartialSumAtZero coefficients n))
    ∣₁
    (constantIsLimitSequence (coefficients zero))


powerSeriesAtZeroSummable : ∀ coefficients →
  PowerSeriesSummableAt coefficients 0ℝ
powerSeriesAtZeroSummable coefficients =
  coefficients zero , powerSeriesAtZeroHasSum coefficients


powerSeriesValueAtZero : ∀ coefficients summable →
  powerSeriesValue coefficients 0ℝ summable
    ≡ coefficients zero
powerSeriesValueAtZero coefficients summable =
  seriesSumIndependent
    (powerSeriesTerms coefficients 0ℝ)
    summable
    (powerSeriesAtZeroSummable coefficients)

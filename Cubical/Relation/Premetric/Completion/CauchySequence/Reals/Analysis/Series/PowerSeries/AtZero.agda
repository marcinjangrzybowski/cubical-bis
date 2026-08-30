module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.AtZero where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (zero ; suc)
import Cubical.Data.Nat.Order as ℕOrder
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform


-- At zero every positive-degree term vanishes.  This generic construction is
-- deliberately independent of a chosen summability modulus and can be used
-- by pointwise, uniform, and locally uniform power-series evaluators alike.

powerSeriesPartialSumAtZero : ∀ coefficients n →
  partialSum (powerSeriesTerms coefficients zeroℝ) (suc n)
    ≡ coefficients zero
powerSeriesPartialSumAtZero coefficients zero =
    add-zero-left (powerSeriesTerms coefficients zeroℝ zero)
  ∙ powerSeriesTerms-zero coefficients
powerSeriesPartialSumAtZero coefficients (suc n) =
    cong₂ Add._+_
      (powerSeriesPartialSumAtZero coefficients n)
      ( cong (coefficients (suc n) Mul.·_) (zeroPowSuc n)
      ∙ mul-zero-right (coefficients (suc n)))
  ∙ add-zero-right (coefficients zero)


powerSeriesAtZeroHasSum : ∀ coefficients →
  HasSum
    (powerSeriesTerms coefficients zeroℝ)
    (coefficients zero)
powerSeriesAtZeroHasSum coefficients =
  eventuallyEqualPresIsLimitSequence
    ∣ suc zero , (λ where
      zero impossible → ⊥.rec (ℕOrder.¬-<-zero impossible)
      (suc n) _ → sym (powerSeriesPartialSumAtZero coefficients n)) ∣₁
    (constantIsLimitSequence (coefficients zero))


powerSeriesValueAtZero : ∀ coefficients summable →
  powerSeriesValue coefficients zeroℝ summable
    ≡ coefficients zero
powerSeriesValueAtZero coefficients summable =
  seriesSumIndependent
    (powerSeriesTerms coefficients zeroℝ)
    (powerSeriesValue coefficients zeroℝ summable , snd summable)
    (coefficients zero , powerSeriesAtZeroHasSum coefficients)


locallyUniformPowerSeriesValueAtZero : ∀ coefficients local →
  locallyUniformPowerSeriesValue coefficients local zeroℝ
    ≡ coefficients zero
locallyUniformPowerSeriesValueAtZero coefficients local =
  seriesSumIndependent
    (powerSeriesTerms coefficients zeroℝ)
    ( locallyUniformPowerSeriesValue coefficients local zeroℝ
    , locallyUniformPowerSeriesValueHasSum coefficients local zeroℝ
    )
    (coefficients zero , powerSeriesAtZeroHasSum coefficients)

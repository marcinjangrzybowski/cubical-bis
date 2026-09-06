module Cubical.Analysis.Real.Sequence.Geometric where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne using (ℕ₊₁)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Sequence
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.Geometric.Base
open import Cubical.Analysis.Real.Series.Geometric.Real

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


opaque
  contractionGeometricBound : (sequence : RealSequence) (q : ℝ) → 0ℝ ≤ℝ q →
    (∀ n → sequence (suc n) ≤ℝ q · sequence n) →
    ∀ n → sequence n ≤ℝ sequence zero · powℝ q n
  contractionGeometricBound sequence q nonnegative contracts zero =
    subst (sequence zero ≤ℝ_) (sym (mulIdR (sequence zero)))
      (≤ℝ-refl (sequence zero))
  contractionGeometricBound sequence q nonnegative contracts (suc n) =
    ≤ℝ-trans (sequence (suc n)) (q · sequence n)
      (sequence zero · powℝ q (suc n)) (contracts n)
      (subst (q · sequence n ≤ℝ_)
        (mulAssoc q (sequence zero) (powℝ q n)
        ∙ cong (_· powℝ q n) (mulComm q (sequence zero))
        ∙ sym (mulAssoc (sequence zero) q (powℝ q n)))
        (mulPres≤L (sequence n) (sequence zero · powℝ q n) q
          (0≤→isNonnegative q nonnegative)
          (contractionGeometricBound sequence q nonnegative contracts n)))


  geometricallyBoundedNonnegativeLimitZero :
    (sequence : RealSequence) (limit q coefficient : ℝ) →
    0ℝ ≤ℝ q → q <ℝ 1ℝ → isLimitSequence sequence limit →
    (∀ n → 0ℝ ≤ℝ sequence n) →
    (∀ n → sequence n ≤ℝ coefficient · powℝ q n) → limit ≡ 0ℝ
  geometricallyBoundedNonnegativeLimitZero sequence limit q coefficient
      nonnegative below converges nonnegative-sequence bounded =
    ≤ℝ-antisym limit 0ℝ
      (limitsPres≤ sequence (λ n → coefficient · powℝ q n) limit 0ℝ
        converges
        (subst (isLimitSequence (λ n → coefficient · powℝ q n))
          (ℝRing.0RightAnnihilates coefficient)
          (mulPresIsLimitSequence
            {x = λ _ → coefficient} {y = geometricTerms q} {l = coefficient} {m = 0ℝ}
            (constantIsLimitSequence coefficient)
            (realGeometricPowersTendToZero q
              (subst (_<ℝ 1ℝ) (sym (absOfNonnegative q nonnegative)) below))))
        bounded)
      (limitsPres≤ (λ _ → 0ℝ) sequence 0ℝ limit
        (constantIsLimitSequence 0ℝ) converges nonnegative-sequence)


successiveIncrements : RealSequence → RealSequence
successiveIncrements sequence n = sequence (suc n) - sequence n


opaque
  initialPlusIncrementSum : ∀ sequence n →
    sequence zero + partialSum (successiveIncrements sequence) n ≡ sequence n
  initialPlusIncrementSum sequence zero = addIdR (sequence zero)
  initialPlusIncrementSum sequence (suc n) =
    addAssoc (sequence zero) (partialSum (successiveIncrements sequence) n)
      (successiveIncrements sequence n)
    ∙ cong (_+ successiveIncrements sequence n)
        (initialPlusIncrementSum sequence n)
    ∙ addComm (sequence n) (sequence (suc n) - sequence n)
    ∙ subAddCancel (sequence (suc n)) (sequence n)


incrementsCauchy→sequenceCauchy : ∀ sequence →
  IsCauchySeries (successiveIncrements sequence) → SeqWitness sequence
incrementsCauchy→sequenceCauchy sequence increments-cauchy =
  subst SeqWitness (funExt (initialPlusIncrementSum sequence))
    (addSeqWitness (constantSeqWitness (sequence zero)) increments-cauchy)


-- A single rational bound on the leading coefficient, together with the
-- explicit geometric modulus, bounds every tail of the increment series.
geometricallyBoundedIncrementsCauchy : ∀ sequence q coefficient →
  0ℝ ≤ℝ q → q <ℝ 1ℝ →
  (∀ n → absℝ (successiveIncrements sequence n)
    ≤ℝ coefficient · powℝ q n) →
  SeqWitness sequence
geometricallyBoundedIncrementsCauchy sequence q coefficient nonnegative below
    dominates = PT.rec squash₁ atBound (∃naturalUpperBound coefficient)
  where
  geometric-cauchy : IsCauchySeries (geometricTerms q)
  geometric-cauchy = realGeometricSeriesIsCauchy q
    (subst (_<ℝ 1ℝ) (sym (absOfNonnegative q nonnegative)) below)

  atBound : (Σ[ n ∈ ℕ₊₁ ] coefficient <ℝ rat (naturalRational n)) →
    SeqWitness sequence
  atBound (bound , strict-bound) =
    incrementsCauchy→sequenceCauchy sequence
      (dominatedCauchySeriesIsCauchy (successiveIncrements sequence)
        (scaleSeries (rat (naturalRational bound)) (geometricTerms q))
        (λ n → ≤ℝ-trans (absℝ (successiveIncrements sequence n))
          (coefficient · powℝ q n)
          (rat (naturalRational bound) · powℝ q n)
          (dominates n)
          (mulPres≤R-0≤ coefficient (rat (naturalRational bound)) (powℝ q n)
            (powNonnegative q n nonnegative)
            (<ℝ-weaken coefficient (rat (naturalRational bound)) strict-bound)))
        (rationalScaleSeriesIsCauchy (naturalRational bound)
          (geometricTerms q) geometric-cauchy))

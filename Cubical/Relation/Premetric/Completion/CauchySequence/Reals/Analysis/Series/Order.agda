module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Order where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (add-monotone)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base


partialSumMono : ∀ a b →
  (∀ n → a n ≤ℝ b n) →
  ∀ n → partialSum a n ≤ℝ partialSum b n
partialSumMono a b pointwise zero =
  ≤ℝ-refl zeroℝ
partialSumMono a b pointwise (suc n) =
  add-monotone
    (partialSum a n) (partialSum b n)
    (a n) (b n)
    (partialSumMono a b pointwise n)
    (pointwise n)


partialSumMonoBefore : ∀ a b n →
  (∀ k → k ℕ.< n → a k ≤ℝ b k) →
  partialSum a n ≤ℝ partialSum b n
partialSumMonoBefore a b zero before =
  ≤ℝ-refl zeroℝ
partialSumMonoBefore a b (suc n) before =
  add-monotone
    (partialSum a n) (partialSum b n)
    (a n) (b n)
    (partialSumMonoBefore a b n
      (λ k k<n → before k (ℕ.<-trans k<n ℕ.<-suc)))
    (before n ℕ.<-suc)


partialSumIndexMono : ∀ terms →
  (∀ n → zeroℝ ≤ℝ terms n) →
  ∀ m n → m ℕ.≤ n →
  partialSum terms m ≤ℝ partialSum terms n
partialSumIndexMono terms nonnegative m n (count , count+m≡n) =
  subst
    (λ k → partialSum terms m ≤ℝ partialSum terms k)
    count+m≡n
    (go count)
  where
  go : ∀ count →
    partialSum terms m ≤ℝ
    partialSum terms (count ℕ.+ m)
  go zero = ≤ℝ-refl (partialSum terms m)
  go (suc count) =
    ≤ℝ-trans
      (partialSum terms m)
      (partialSum terms (count ℕ.+ m))
      (partialSum terms (count ℕ.+ m) Add.+
        terms (count ℕ.+ m))
      (go count)
      (subst
        (λ z → z ≤ℝ
          partialSum terms (count ℕ.+ m) Add.+
            terms (count ℕ.+ m))
        (add-zero-right (partialSum terms (count ℕ.+ m)))
        (add-monotone
          (partialSum terms (count ℕ.+ m))
          (partialSum terms (count ℕ.+ m))
          zeroℝ (terms (count ℕ.+ m))
          (≤ℝ-refl (partialSum terms (count ℕ.+ m)))
          (nonnegative (count ℕ.+ m))))


partialSumNonnegative : ∀ terms →
  (∀ n → zeroℝ ≤ℝ terms n) →
  ∀ n → zeroℝ ≤ℝ partialSum terms n
partialSumNonnegative terms nonnegative n =
  subst (λ z → z ≤ℝ partialSum terms n)
    (partialSum-zero terms)
    (partialSumIndexMono
      terms nonnegative zero n ℕ.zero-≤)


seriesSumMono : ∀ a b →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  (∀ n → a n ≤ℝ b n) →
  seriesSum a a-summable ≤ℝ
  seriesSum b b-summable
seriesSumMono a b a-summable b-summable pointwise =
  pointwiseLePresLimits
    (partialSumMono a b pointwise)
    (seriesSumHasSum a a-summable)
    (seriesSumHasSum b b-summable)


seriesSumNonnegative : ∀ terms →
  (summable : Summable terms) →
  (∀ n → zeroℝ ≤ℝ terms n) →
  zeroℝ ≤ℝ seriesSum terms summable
seriesSumNonnegative terms summable nonnegative =
  subst (λ z → z ≤ℝ seriesSum terms summable)
    seriesSum-zero
    (seriesSumMono
      (λ _ → zeroℝ) terms
      zeroSeriesSummable summable
      nonnegative)


-- For nonnegative terms, every finite partial sum lies below the sum.  The
-- proof uses a merely existing eventual lower-bound cutoff, matching the
-- public order relation on sequences.

partialSumLeSeriesSum : ∀ terms →
  (summable : Summable terms) →
  (∀ n → zeroℝ ≤ℝ terms n) →
  ∀ n → partialSum terms n ≤ℝ seriesSum terms summable
partialSumLeSeriesSum terms summable nonnegative n =
  eventuallyLowerBoundPresLimit
    {x = partialSum terms}
    {l = seriesSum terms summable}
    {b = partialSum terms n}
    ∣ n , (λ k n≤k →
      partialSumIndexMono terms nonnegative n k n≤k) ∣₁
    (seriesSumHasSum terms summable)

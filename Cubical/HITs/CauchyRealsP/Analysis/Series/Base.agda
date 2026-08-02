module Cubical.HITs.CauchyRealsP.Analysis.Series.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)
  renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence.Cauchy

RealSequence : Type
RealSequence =
  ℕ → ℝ

partialSum : RealSequence → RealSequence
partialSum terms zero =
  0
partialSum terms (suc n) =
  partialSum terms n + terms n

partialSum-zero : ∀ terms →
  partialSum terms zero ≡ 0
partialSum-zero terms =
  refl

partialSum-step : ∀ terms n →
  partialSum terms (suc n) ≡
  partialSum terms n + terms n
partialSum-step terms n =
  refl

partialSum-pointwise : ∀ a b →
  (∀ n → a n ≡ b n) →
  ∀ n →
  partialSum a n ≡ partialSum b n
partialSum-pointwise a b pointwise zero =
  refl
partialSum-pointwise a b pointwise (suc n) =
  cong₂ _+_
    (partialSum-pointwise
      a b pointwise n)
    (pointwise n)

partialSum-pointwiseBefore : ∀ a b n →
  (∀ k → k ℕ.< n → a k ≡ b k) →
  partialSum a n ≡ partialSum b n
partialSum-pointwiseBefore a b zero before =
  refl
partialSum-pointwiseBefore a b (suc n) before =
  cong₂ _+_
    (partialSum-pointwiseBefore
      a b n
      (λ k k<n →
        before k
          (ℕ.<-trans k<n ℕ.<-suc)))
    (before n ℕ.<-suc)

partialSum-add : ∀ a b n →
  partialSum (λ k → a k + b k) n ≡
  partialSum a n + partialSum b n
partialSum-add a b zero =
  sym (addIdR 0)
partialSum-add a b (suc n) =
  cong (_+ (a n + b n))
    (partialSum-add a b n)
  ∙ sym
      (addAssoc
        (partialSum a n)
        (partialSum b n)
        (a n + b n))
  ∙ cong (partialSum a n +_)
      (addAssoc
        (partialSum b n)
        (a n) (b n))
  ∙ cong
      (λ z → partialSum a n + (z + b n))
      (addComm (partialSum b n) (a n))
  ∙ cong (partialSum a n +_)
      (sym
        (addAssoc
          (a n)
          (partialSum b n)
          (b n)))
  ∙ addAssoc
      (partialSum a n)
      (a n)
      (partialSum b n + b n)

partialSum-neg : ∀ a n →
  partialSum (λ k → - a k) n ≡
  - partialSum a n
partialSum-neg a zero =
  sym negZero
partialSum-neg a (suc n) =
  cong (_+ (- a n))
    (partialSum-neg a n)
  ∙ sym
      (negAdd
        (partialSum a n)
        (a n))

partialSum-sub : ∀ a b n →
  partialSum (λ k → a k - b k) n ≡
  partialSum a n - partialSum b n
partialSum-sub a b n =
  partialSum-add a (λ k → - b k) n
  ∙ cong (partialSum a n +_)
      (partialSum-neg b n)

partialSum-zeroSequence : ∀ n →
  partialSum (λ _ → 0) n ≡ 0
partialSum-zeroSequence zero =
  refl
partialSum-zeroSequence (suc n) =
  cong (_+ 0) (partialSum-zeroSequence n)
  ∙ addIdR 0

partialSumDifference : ∀ terms n →
  partialSum terms (suc n)
    - partialSum terms n ≡
  terms n
partialSumDifference terms n =
  cong (_- partialSum terms n)
    (addComm (partialSum terms n) (terms n))
  ∙ addSubCancel
      (terms n) (partialSum terms n)

partialSumMono : ∀ a b →
  (∀ n → a n ≤ℝ b n) →
  ∀ n →
  partialSum a n ≤ℝ partialSum b n
partialSumMono a b pointwise≤ zero =
  ≤ℝ-refl 0
partialSumMono a b pointwise≤ (suc n) =
  ≤ℝ-add
    (partialSum a n) (partialSum b n)
    (a n) (b n)
    (partialSumMono a b pointwise≤ n)
    (pointwise≤ n)

partialSumMonoBefore : ∀ a b n →
  (∀ k → k ℕ.< n → a k ≤ℝ b k) →
  partialSum a n ≤ℝ partialSum b n
partialSumMonoBefore a b zero before =
  ≤ℝ-refl 0
partialSumMonoBefore a b (suc n) before =
  ≤ℝ-add
    (partialSum a n) (partialSum b n)
    (a n) (b n)
    (partialSumMonoBefore
      a b n
      (λ k k<n →
        before k
          (ℕ.<-trans k<n ℕ.<-suc)))
    (before n ℕ.<-suc)

partialSumIndexMono :
  ∀ terms →
  (∀ n → 0 ≤ℝ terms n) →
  ∀ m n →
  m ℕ.≤ n →
  partialSum terms m ≤ℝ partialSum terms n
partialSumIndexMono
  terms nonnegative m n (count , count+m≡n) =
    subst
      (λ k →
        partialSum terms m ≤ℝ
        partialSum terms k)
      count+m≡n
      (go count)
  where
  go : ∀ count →
    partialSum terms m ≤ℝ
    partialSum terms (count +ℕ m)
  go zero =
    ≤ℝ-refl (partialSum terms m)
  go (suc count) =
    ≤ℝ-trans
      (partialSum terms m)
      (partialSum terms (count +ℕ m))
      ( partialSum terms (count +ℕ m)
      + terms (count +ℕ m)
      )
      (go count)
      (subst
        (_≤ℝ
          partialSum terms (count +ℕ m)
            + terms (count +ℕ m))
        (addIdR
          (partialSum terms
            (count +ℕ m)))
        (≤ℝ-add
          (partialSum terms (count +ℕ m))
          (partialSum terms (count +ℕ m))
          0
          (terms (count +ℕ m))
          (≤ℝ-refl
            (partialSum terms (count +ℕ m)))
          (nonnegative (count +ℕ m))))

partialSumNonnegative : ∀ terms →
  (∀ n → 0 ≤ℝ terms n) →
  ∀ n →
  0 ≤ℝ partialSum terms n
partialSumNonnegative terms nonnegative n =
  subst
    (_≤ℝ partialSum terms n)
    (sym (partialSum-zero terms))
    (partialSumIndexMono
      terms nonnegative zero n
      ℕ.zero-≤)

partialSumAbsBound : ∀ terms n →
  absℝ (partialSum terms n) ≤ℝ
  partialSum (absℝ ∘ terms) n
partialSumAbsBound terms zero =
  subst (_≤ℝ 0)
    (sym absZero)
    (≤ℝ-refl 0)
partialSumAbsBound terms (suc n) =
  ≤ℝ-trans
    (absℝ
      (partialSum terms n + terms n))
    (absℝ (partialSum terms n)
      + absℝ (terms n))
    (partialSum (absℝ ∘ terms) n
      + absℝ (terms n))
    (absTriangle
      (partialSum terms n) (terms n))
    (≤ℝ-add
      (absℝ (partialSum terms n))
      (partialSum (absℝ ∘ terms) n)
      (absℝ (terms n)) (absℝ (terms n))
      (partialSumAbsBound terms n)
      (≤ℝ-refl (absℝ (terms n))))

HasSum : RealSequence → ℝ → Type
HasSum terms value =
  isLimitSeq (partialSum terms) value

Summable : RealSequence → Type
Summable terms =
  limitSeq (partialSum terms)

isPropSummable : ∀ terms →
  isProp (Summable terms)
isPropSummable terms =
  isPropLimitSeq (partialSum terms)

IsCauchySeries : RealSequence → Type
IsCauchySeries terms =
  isCauchySeq (partialSum terms)

cauchySeriesIsSummable : ∀ terms →
  IsCauchySeries terms →
  Summable terms
cauchySeriesIsSummable terms =
  cauchySequenceLimit (partialSum terms)

seriesSum : ∀ terms →
  Summable terms →
  ℝ
seriesSum terms summable =
  fst summable

seriesSumHasSum : ∀ terms summable →
  HasSum terms (seriesSum terms summable)
seriesSumHasSum terms summable =
  snd summable

seriesSumIndependent : ∀ terms
  (p q : Summable terms) →
  seriesSum terms p ≡ seriesSum terms q
seriesSumIndependent terms p q =
  cong fst (isPropSummable terms p q)

seriesSumPresPath :
  ∀ a b →
  a ≡ b →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  seriesSum a a-summable
    ≡
  seriesSum b b-summable
seriesSumPresPath
  a b a≡b a-summable b-summable =
    sym
      (seriesSumIndependent
        b b-summable target-summable)
  where
  target-summable : Summable b
  target-summable =
    seriesSum a a-summable
    , subst
        (λ terms →
          HasSum terms
            (seriesSum a a-summable))
        a≡b
        (seriesSumHasSum a a-summable)

zeroSeriesSummable :
  Summable (λ _ → 0)
zeroSeriesSummable =
  0
  , eventuallyEqualSeqPresIsLimitSeq
      (λ _ → 0)
      (partialSum (λ _ → 0))
      0
      (0 , λ n _ →
        sym (partialSum-zeroSequence n))
      (constantIsLimitSeq 0)

negSummable : ∀ terms →
  Summable terms →
  Summable (λ n → - terms n)
negSummable terms summable =
  - seriesSum terms summable
  , eventuallyEqualSeqPresIsLimitSeq
      (λ n → - partialSum terms n)
      (partialSum (λ n → - terms n))
      (- seriesSum terms summable)
      (0 , λ n _ →
        sym (partialSum-neg terms n))
      (negPresIsLimitSeq
        (partialSum terms)
        (seriesSum terms summable)
        (seriesSumHasSum terms summable))

addSummable : ∀ a b →
  Summable a →
  Summable b →
  Summable (λ n → a n + b n)
addSummable a b a-summable b-summable =
  seriesSum a a-summable + seriesSum b b-summable
  , eventuallyEqualSeqPresIsLimitSeq
      (λ n → partialSum a n + partialSum b n)
      (partialSum (λ n → a n + b n))
      (seriesSum a a-summable + seriesSum b b-summable)
      (0 , λ n _ →
        sym (partialSum-add a b n))
      (addPresIsLimitSeq
        (partialSum a) (partialSum b)
        (seriesSum a a-summable)
        (seriesSum b b-summable)
        (seriesSumHasSum a a-summable)
        (seriesSumHasSum b b-summable))

subSummable : ∀ a b →
  Summable a →
  Summable b →
  Summable (λ n → a n - b n)
subSummable a b a-summable b-summable =
  addSummable
    a (λ n → - b n)
    a-summable
    (negSummable b b-summable)

seriesSum-zero :
  seriesSum (λ _ → 0) zeroSeriesSummable ≡ 0
seriesSum-zero =
  refl

seriesSum-neg : ∀ terms
  (summable : Summable terms)
  (neg-summable : Summable (λ n → - terms n)) →
  seriesSum (λ n → - terms n) neg-summable ≡
  - seriesSum terms summable
seriesSum-neg terms summable neg-summable =
  seriesSumIndependent
    (λ n → - terms n)
    neg-summable
    (negSummable terms summable)

seriesSum-add : ∀ a b
  (a-summable : Summable a)
  (b-summable : Summable b)
  (sum-summable : Summable (λ n → a n + b n)) →
  seriesSum (λ n → a n + b n) sum-summable ≡
  seriesSum a a-summable + seriesSum b b-summable
seriesSum-add a b a-summable b-summable sum-summable =
  seriesSumIndependent
    (λ n → a n + b n)
    sum-summable
    (addSummable a b a-summable b-summable)

seriesSum-sub : ∀ a b
  (a-summable : Summable a)
  (b-summable : Summable b)
  (difference-summable :
    Summable (λ n → a n - b n)) →
  seriesSum
    (λ n → a n - b n)
    difference-summable ≡
  seriesSum a a-summable
    - seriesSum b b-summable
seriesSum-sub a b
  a-summable b-summable difference-summable =
    seriesSumIndependent
      (λ n → a n - b n)
      difference-summable
      (subSummable a b a-summable b-summable)

seriesSumMono : ∀ a b →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  (∀ n → a n ≤ℝ b n) →
  seriesSum a a-summable ≤ℝ
  seriesSum b b-summable
seriesSumMono a b a-summable b-summable pointwise≤ =
  pointwiseLeSeqPresLimit
    (partialSum a) (partialSum b)
    (seriesSum a a-summable)
    (seriesSum b b-summable)
    (partialSumMono a b pointwise≤)
    (seriesSumHasSum a a-summable)
    (seriesSumHasSum b b-summable)

seriesSumNonnegative : ∀ terms →
  (summable : Summable terms) →
  (∀ n → 0 ≤ℝ terms n) →
  0 ≤ℝ seriesSum terms summable
seriesSumNonnegative terms summable termsNonnegative =
  subst
    (_≤ℝ seriesSum terms summable)
    seriesSum-zero
    (seriesSumMono
      (λ _ → 0) terms
      zeroSeriesSummable summable
      termsNonnegative)

seriesSumAbsBound : ∀ terms →
  (summable : Summable terms) →
  (abs-summable : Summable (absℝ ∘ terms)) →
  absℝ (seriesSum terms summable) ≤ℝ
  seriesSum (absℝ ∘ terms) abs-summable
seriesSumAbsBound terms summable abs-summable =
  pointwiseLeSeqPresLimit
    (absℝ ∘ partialSum terms)
    (partialSum (absℝ ∘ terms))
    (absℝ (seriesSum terms summable))
    (seriesSum (absℝ ∘ terms) abs-summable)
    (partialSumAbsBound terms)
    (absPresIsLimitSeq
      (partialSum terms)
      (seriesSum terms summable)
      (seriesSumHasSum terms summable))
    (seriesSumHasSum
      (absℝ ∘ terms) abs-summable)

summableTermsTendToZero : ∀ terms →
  Summable terms →
  isLimitSeq terms 0
summableTermsTendToZero terms summable =
  eventuallyEqualSeqPresIsLimitSeq
    differenceSequence terms 0
    (0 , λ n _ →
      partialSumDifference terms n)
    differenceLimit
  where
  sum : ℝ
  sum =
    seriesSum terms summable

  partialSums : RealSequence
  partialSums =
    partialSum terms

  differenceSequence : RealSequence
  differenceSequence n =
    partialSums (suc n) - partialSums n

  shiftedPartialSumsLimit :
    isLimitSeq (shiftSeq 1 partialSums) sum
  shiftedPartialSumsLimit =
    shiftPresIsLimitSeq
      1 partialSums sum
      (seriesSumHasSum terms summable)

  differenceLimitAtSelfDifference :
    isLimitSeq differenceSequence (sum - sum)
  differenceLimitAtSelfDifference =
    subPresIsLimitSeq
      (shiftSeq 1 partialSums)
      partialSums sum sum
      shiftedPartialSumsLimit
      (seriesSumHasSum terms summable)

  differenceLimit :
    isLimitSeq differenceSequence 0
  differenceLimit =
    subst
      (isLimitSeq differenceSequence)
      (subSelf sum)
      differenceLimitAtSelfDifference

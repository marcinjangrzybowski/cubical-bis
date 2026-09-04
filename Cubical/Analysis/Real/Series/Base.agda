module Cubical.Analysis.Real.Series.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Sequence


RealSequence : Type₀
RealSequence = ℕ → ℝ


partialSum : RealSequence → RealSequence
partialSum terms zero = 0ℝ
partialSum terms (suc n) =
  partialSum terms n + terms n


partialSum-zero : ∀ terms →
  partialSum terms zero ≡ 0ℝ
partialSum-zero terms = refl


partialSum-step : ∀ terms n →
  partialSum terms (suc n) ≡
  partialSum terms n + terms n
partialSum-step terms n = refl


partialSum-pointwise : ∀ a b →
  (∀ n → a n ≡ b n) →
  ∀ n → partialSum a n ≡ partialSum b n
partialSum-pointwise a b pointwise zero = refl
partialSum-pointwise a b pointwise (suc n) =
  cong₂ _+_
    (partialSum-pointwise a b pointwise n)
    (pointwise n)


partialSum-add : ∀ a b n →
  partialSum (λ k → a k + b k) n ≡
  partialSum a n + partialSum b n
partialSum-add a b zero = sym (addIdR 0ℝ)
partialSum-add a b (suc n) =
    cong (_+ (a n + b n))
      (partialSum-add a b n)
  ∙ sym
      (addAssoc
        (partialSum a n) (partialSum b n) (a n + b n))
  ∙ cong (partialSum a n +_)
      (addAssoc (partialSum b n) (a n) (b n))
  ∙ cong
      (λ z → partialSum a n + (z + b n))
      (addComm (partialSum b n) (a n))
  ∙ cong (partialSum a n +_)
      (sym (addAssoc (a n) (partialSum b n) (b n)))
  ∙ addAssoc
      (partialSum a n) (a n)
      (partialSum b n + b n)


partialSum-neg : ∀ a n →
  partialSum (-_ ∘ a) n ≡
  - partialSum a n
partialSum-neg a zero = sym negZero
partialSum-neg a (suc n) =
  cong (_+ (- a n)) (partialSum-neg a n)
  ∙ sym (negAdd (partialSum a n) (a n))


partialSum-sub : ∀ a b n →
  partialSum (λ k → a k - b k) n ≡
  partialSum a n - partialSum b n
partialSum-sub a b n =
  partialSum-add a (-_ ∘ b) n
  ∙ cong (partialSum a n +_) (partialSum-neg b n)


partialSum-zeroSequence : ∀ n →
  partialSum (λ _ → 0ℝ) n ≡ 0ℝ
partialSum-zeroSequence zero = refl
partialSum-zeroSequence (suc n) =
  cong (_+ 0ℝ) (partialSum-zeroSequence n)
  ∙ addIdR 0ℝ


partialSumDifference : ∀ terms n →
  partialSum terms (suc n) - partialSum terms n ≡
  terms n
partialSumDifference terms n =
    cong (_- partialSum terms n)
      (addComm (partialSum terms n) (terms n))
  ∙ sym
      (addAssoc
        (terms n) (partialSum terms n)
        (- partialSum terms n))
  ∙ cong (terms n +_) (addInvR (partialSum terms n))
  ∙ addIdR (terms n)


HasSum : RealSequence → ℝ → Type₀
HasSum terms value =
  isLimitSequence (partialSum terms) value


Summable : RealSequence → Type₀
Summable terms = SequenceLimit (partialSum terms)


isPropSummable : ∀ terms → isProp (Summable terms)
isPropSummable terms =
  isPropSequenceLimit (partialSum terms)


IsCauchySeries : RealSequence → Type₀
IsCauchySeries terms = SeqWitness (partialSum terms)


isPropIsCauchySeries : ∀ terms →
  isProp (IsCauchySeries terms)
isPropIsCauchySeries terms = squash₁


cauchySeriesIsSummable : ∀ terms →
  IsCauchySeries terms → Summable terms
cauchySeriesIsSummable terms =
  sequenceLimit (partialSum terms)


seriesSum : ∀ terms → Summable terms → ℝ
seriesSum terms summable = fst summable


seriesSumHasSum : ∀ terms summable →
  HasSum terms (seriesSum terms summable)
seriesSumHasSum terms summable = snd summable


seriesSumIndependent : ∀ terms
  (p q : Summable terms) →
  seriesSum terms p ≡ seriesSum terms q
seriesSumIndependent terms p q =
  cong fst (isPropSummable terms p q)


seriesSumPresPath : ∀ a b →
  a ≡ b →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  seriesSum a a-summable ≡ seriesSum b b-summable
seriesSumPresPath a b a≡b a-summable b-summable =
  sym (seriesSumIndependent b b-summable target-summable)
  where
  target-summable : Summable b
  target-summable =
    seriesSum a a-summable
    , subst
        (λ terms → HasSum terms (seriesSum a a-summable))
        a≡b
        (seriesSumHasSum a a-summable)


zeroSeriesSummable : Summable (λ _ → 0ℝ)
zeroSeriesSummable =
  0ℝ
  , subst
      (λ sequence → isLimitSequence sequence 0ℝ)
      (funExt λ n → sym (partialSum-zeroSequence n))
      (constantIsLimitSequence 0ℝ)


negSummable : ∀ terms →
  Summable terms → Summable (-_ ∘ terms)
negSummable terms summable =
  - seriesSum terms summable
  , subst
      (λ sequence →
        isLimitSequence sequence (- seriesSum terms summable))
      (funExt λ n → sym (partialSum-neg terms n))
      (negPresIsLimitSequence
        (seriesSumHasSum terms summable))


addSummable : ∀ a b →
  Summable a → Summable b →
  Summable (λ n → a n + b n)
addSummable a b a-summable b-summable =
  seriesSum a a-summable + seriesSum b b-summable
  , subst
      (λ sequence → isLimitSequence sequence
        (seriesSum a a-summable + seriesSum b b-summable))
      (funExt λ n → sym (partialSum-add a b n))
      (addPresIsLimitSequence
        (seriesSumHasSum a a-summable)
        (seriesSumHasSum b b-summable))


subSummable : ∀ a b →
  Summable a → Summable b →
  Summable (λ n → a n - b n)
subSummable a b a-summable b-summable =
  addSummable a (-_ ∘ b)
    a-summable (negSummable b b-summable)


seriesSum-zero :
  seriesSum (λ _ → 0ℝ) zeroSeriesSummable ≡ 0ℝ
seriesSum-zero = refl


seriesSum-neg : ∀ terms
  (summable : Summable terms)
  (neg-summable : Summable (-_ ∘ terms)) →
  seriesSum (-_ ∘ terms) neg-summable ≡
  - seriesSum terms summable
seriesSum-neg terms summable neg-summable =
  seriesSumIndependent
    (-_ ∘ terms) neg-summable
    (negSummable terms summable)


seriesSum-add : ∀ a b
  (a-summable : Summable a)
  (b-summable : Summable b)
  (sum-summable : Summable (λ n → a n + b n)) →
  seriesSum (λ n → a n + b n) sum-summable ≡
  seriesSum a a-summable + seriesSum b b-summable
seriesSum-add a b a-summable b-summable sum-summable =
  seriesSumIndependent
    (λ n → a n + b n) sum-summable
    (addSummable a b a-summable b-summable)


seriesSum-sub : ∀ a b
  (a-summable : Summable a)
  (b-summable : Summable b)
  (difference-summable : Summable (λ n → a n - b n)) →
  seriesSum (λ n → a n - b n) difference-summable ≡
  seriesSum a a-summable - seriesSum b b-summable
seriesSum-sub a b a-summable b-summable difference-summable =
  seriesSumIndependent
    (λ n → a n - b n) difference-summable
    (subSummable a b a-summable b-summable)


summableTermsTendToZero : ∀ terms →
  Summable terms → isLimitSequence terms 0ℝ
summableTermsTendToZero terms summable =
  subst
    (λ sequence → isLimitSequence sequence 0ℝ)
    (funExt (partialSumDifference terms))
    (convergentSuccessiveDifferences→zero
      (partialSum terms) (seriesSum terms summable)
      (seriesSumHasSum terms summable))

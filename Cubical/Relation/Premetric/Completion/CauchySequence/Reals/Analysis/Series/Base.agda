module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence


zeroℝ : Real.ℝ
zeroℝ = CommRingStr.0r (snd ℝCommRing)


RealSequence : Type₀
RealSequence = ℕ → Real.ℝ


partialSum : RealSequence → RealSequence
partialSum terms zero = zeroℝ
partialSum terms (suc n) =
  partialSum terms n Add.+ terms n


partialSum-zero : ∀ terms →
  partialSum terms zero ≡ zeroℝ
partialSum-zero terms = refl


partialSum-step : ∀ terms n →
  partialSum terms (suc n) ≡
  partialSum terms n Add.+ terms n
partialSum-step terms n = refl


partialSum-pointwise : ∀ a b →
  (∀ n → a n ≡ b n) →
  ∀ n → partialSum a n ≡ partialSum b n
partialSum-pointwise a b pointwise zero = refl
partialSum-pointwise a b pointwise (suc n) =
  cong₂ Add._+_
    (partialSum-pointwise a b pointwise n)
    (pointwise n)


partialSum-pointwiseBefore : ∀ a b n →
  (∀ k → k ℕ.< n → a k ≡ b k) →
  partialSum a n ≡ partialSum b n
partialSum-pointwiseBefore a b zero before = refl
partialSum-pointwiseBefore a b (suc n) before =
  cong₂ Add._+_
    (partialSum-pointwiseBefore a b n
      (λ k k<n → before k (ℕ.<-trans k<n ℕ.<-suc)))
    (before n ℕ.<-suc)


partialSum-add : ∀ a b n →
  partialSum (λ k → a k Add.+ b k) n ≡
  partialSum a n Add.+ partialSum b n
partialSum-add a b zero =
  sym (add-zero-right zeroℝ)
partialSum-add a b (suc n) =
    cong (Add._+ (a n Add.+ b n))
      (partialSum-add a b n)
  ∙ sym (add-assoc
      (partialSum a n) (partialSum b n) (a n Add.+ b n))
  ∙ cong (partialSum a n Add.+_)
      (add-assoc (partialSum b n) (a n) (b n))
  ∙ cong
      (λ z → partialSum a n Add.+ (z Add.+ b n))
      (add-comm (partialSum b n) (a n))
  ∙ cong (partialSum a n Add.+_)
      (sym (add-assoc (a n) (partialSum b n) (b n)))
  ∙ add-assoc
      (partialSum a n) (a n)
      (partialSum b n Add.+ b n)


partialSum-neg : ∀ a n →
  partialSum (Neg.-_ ∘ a) n ≡
  Neg.- partialSum a n
partialSum-neg a zero = sym neg-zero
partialSum-neg a (suc n) =
    cong (Add._+ (Neg.- a n)) (partialSum-neg a n)
  ∙ sym (neg-add (partialSum a n) (a n))


partialSum-sub : ∀ a b n →
  partialSum (λ k → a k Group.- b k) n ≡
  partialSum a n Group.- partialSum b n
partialSum-sub a b n =
  partialSum-add a (Neg.-_ ∘ b) n
  ∙ cong (partialSum a n Add.+_) (partialSum-neg b n)


partialSum-zeroSequence : ∀ n →
  partialSum (λ _ → zeroℝ) n ≡ zeroℝ
partialSum-zeroSequence zero = refl
partialSum-zeroSequence (suc n) =
  cong (Add._+ zeroℝ) (partialSum-zeroSequence n)
  ∙ add-zero-right zeroℝ


partialSumDifference : ∀ terms n →
  partialSum terms (suc n) Group.- partialSum terms n ≡
  terms n
partialSumDifference terms n =
  cong (Group._- partialSum terms n)
    (add-comm (partialSum terms n) (terms n))
  ∙ add-sub-cancel (terms n) (partialSum terms n)


-- Series are deliberately defined through the native sequence notions.
-- `IsCauchySeries` therefore asks only for a truncated tail independently
-- at every radius, rather than for a chosen modulus for all radii.

HasSum : RealSequence → Real.ℝ → Type₀
HasSum terms value =
  isLimitSequence (partialSum terms) value


Summable : RealSequence → Type₀
Summable terms =
  SequenceLimit (partialSum terms)


isPropSummable : ∀ terms → isProp (Summable terms)
isPropSummable terms =
  isPropSequenceLimit (partialSum terms)


IsCauchySeries : RealSequence → Type₀
IsCauchySeries terms =
  IsCauchySequence (partialSum terms)


isPropIsCauchySeries : ∀ terms →
  isProp (IsCauchySeries terms)
isPropIsCauchySeries terms =
  isPropIsCauchySequence (partialSum terms)


cauchySeriesIsSummable : ∀ terms →
  IsCauchySeries terms → Summable terms
cauchySeriesIsSummable terms =
  cauchySequenceLimit (partialSum terms)


summableIsCauchySeries : ∀ terms →
  Summable terms → IsCauchySeries terms
summableIsCauchySeries terms =
  sequenceLimit→isCauchySequence


-- Unlike the traditional chosen-modulus presentation, completeness gives
-- an equivalence at exactly the native strength: no tail-choice principle
-- is needed in either direction.

isCauchySeries≃summable : ∀ terms →
  IsCauchySeries terms ≃ Summable terms
isCauchySeries≃summable terms =
  isCauchySequence≃sequenceLimit (partialSum terms)


seriesSum : ∀ terms → Summable terms → Real.ℝ
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


zeroSeriesSummable : Summable (λ _ → zeroℝ)
zeroSeriesSummable =
  zeroℝ
  , eventuallyEqualPresIsLimitSequence
      ∣ 0 , (λ n _ → sym (partialSum-zeroSequence n)) ∣₁
      (constantIsLimitSequence zeroℝ)


negSummable : ∀ terms →
  Summable terms → Summable (Neg.-_ ∘ terms)
negSummable terms summable =
  Neg.- seriesSum terms summable
  , eventuallyEqualPresIsLimitSequence
      ∣ 0 , (λ n _ → sym (partialSum-neg terms n)) ∣₁
      (negPresIsLimitSequence (seriesSumHasSum terms summable))


addSummable : ∀ a b →
  Summable a → Summable b →
  Summable (λ n → a n Add.+ b n)
addSummable a b a-summable b-summable =
  seriesSum a a-summable Add.+ seriesSum b b-summable
  , eventuallyEqualPresIsLimitSequence
      ∣ 0 , (λ n _ → sym (partialSum-add a b n)) ∣₁
      (addPresIsLimitSequence
        (seriesSumHasSum a a-summable)
        (seriesSumHasSum b b-summable))


subSummable : ∀ a b →
  Summable a → Summable b →
  Summable (λ n → a n Group.- b n)
subSummable a b a-summable b-summable =
  addSummable a (Neg.-_ ∘ b)
    a-summable (negSummable b b-summable)


seriesSum-zero :
  seriesSum (λ _ → zeroℝ) zeroSeriesSummable ≡ zeroℝ
seriesSum-zero = refl


seriesSum-neg : ∀ terms
  (summable : Summable terms)
  (neg-summable : Summable (Neg.-_ ∘ terms)) →
  seriesSum (Neg.-_ ∘ terms) neg-summable ≡
  Neg.- seriesSum terms summable
seriesSum-neg terms summable neg-summable =
  seriesSumIndependent
    (Neg.-_ ∘ terms) neg-summable
    (negSummable terms summable)


seriesSum-add : ∀ a b
  (a-summable : Summable a)
  (b-summable : Summable b)
  (sum-summable : Summable (λ n → a n Add.+ b n)) →
  seriesSum (λ n → a n Add.+ b n) sum-summable ≡
  seriesSum a a-summable Add.+ seriesSum b b-summable
seriesSum-add a b a-summable b-summable sum-summable =
  seriesSumIndependent
    (λ n → a n Add.+ b n) sum-summable
    (addSummable a b a-summable b-summable)


seriesSum-sub : ∀ a b
  (a-summable : Summable a)
  (b-summable : Summable b)
  (difference-summable :
    Summable (λ n → a n Group.- b n)) →
  seriesSum (λ n → a n Group.- b n) difference-summable ≡
  seriesSum a a-summable Group.- seriesSum b b-summable
seriesSum-sub a b a-summable b-summable difference-summable =
  seriesSumIndependent
    (λ n → a n Group.- b n) difference-summable
    (subSummable a b a-summable b-summable)


-- The standard necessary condition for summability also avoids choosing a
-- modulus.  It compares the term sequence merely eventually with the
-- difference of two convergent partial-sum sequences.

summableTermsTendToZero : ∀ terms →
  Summable terms → isLimitSequence terms zeroℝ
summableTermsTendToZero terms summable =
  eventuallyEqualPresIsLimitSequence
    ∣ 0 , (λ n _ → partialSumDifference terms n) ∣₁
    difference-limit
  where
  sum : Real.ℝ
  sum = seriesSum terms summable

  partialSums : RealSequence
  partialSums = partialSum terms

  differenceSequence : RealSequence
  differenceSequence n =
    partialSums (suc n) Group.- partialSums n

  shifted-partial-sums-limit :
    isLimitSequence (shiftSequence 1 partialSums) sum
  shifted-partial-sums-limit =
    shiftPresIsLimitSequence 1 partialSums sum
      (seriesSumHasSum terms summable)

  difference-limit-at-self-difference :
    isLimitSequence differenceSequence (sum Group.- sum)
  difference-limit-at-self-difference =
    subPresIsLimitSequence
      shifted-partial-sums-limit
      (seriesSumHasSum terms summable)

  difference-limit :
    isLimitSequence differenceSequence zeroℝ
  difference-limit =
    subst (isLimitSequence differenceSequence)
      (sub-self sum)
      difference-limit-at-self-difference

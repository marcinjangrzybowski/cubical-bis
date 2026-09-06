module Cubical.Analysis.Real.Series.Product.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc; _∸_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
  using (subAddCancel)
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.FiniteSum.Reindexing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Bounds
open import Cubical.Analysis.Real.Series.Operations


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  addSubCancel : ∀ x y → (x + y) - y ≡ x
  addSubCancel x y =
    sym (addAssoc x y (- y))
    ∙ cong (x +_) (addInvR y)
    ∙ addIdR x


-- A bounded pointwise equality is enough to reindex an initial-segment sum.
partialSum-pointwiseBefore : ∀ a b n →
  (∀ k → k ℕ.< n → a k ≡ b k) →
  partialSum a n ≡ partialSum b n
partialSum-pointwiseBefore a b zero before = refl
partialSum-pointwiseBefore a b (suc n) before =
  cong₂ _+_
    (partialSum-pointwiseBefore a b n
      (λ k k<n → before k (ℕ.<-trans k<n ℕ.<-suc)))
    (before n ℕ.<-suc)


-- The Cauchy product is the sum along each finite anti-diagonal.
cauchyProduct :
  RealSequence → RealSequence → RealSequence
cauchyProduct a b =
  diagonalSum (λ i j → a i · b j)


convolution :
  RealSequence → RealSequence → RealSequence
convolution = cauchyProduct


cauchyProduct-zero : ∀ a b →
  cauchyProduct a b zero ≡ a zero · b zero
cauchyProduct-zero a b =
  diagonalSum-zero (λ i j → a i · b j)


cauchyProduct-left-step : ∀ a b n →
  cauchyProduct a b (suc n) ≡
  a zero · b (suc n)
    + cauchyProduct (a ∘ suc) b n
cauchyProduct-left-step a b n =
  diagonalSum-first (λ i j → a i · b j) n


cauchyProduct-comm : ∀ a b n →
  cauchyProduct a b n ≡ cauchyProduct b a n
cauchyProduct-comm a b n =
  partialSum-reverse
    (λ k → a k · b (n ∸ k)) n
  ∙ partialSum-pointwiseBefore
      (λ k → a (n ∸ k) · b (n ∸ (n ∸ k)))
      (λ k → b k · a (n ∸ k))
      (suc n)
      summandPath
  where
  summandPath : ∀ k → k ℕ.< suc n →
    a (n ∸ k) · b (n ∸ (n ∸ k)) ≡
    b k · a (n ∸ k)
  summandPath k k<sucn =
    cong (a (n ∸ k) ·_)
      (cong b
        (sym
          (boundedSubtractInvolutive
            k n (ℕ.pred-≤-pred k<sucn))))
    ∙ mulComm (a (n ∸ k)) (b k)


cauchyProduct-comm-sequence : ∀ a b →
  cauchyProduct a b ≡ cauchyProduct b a
cauchyProduct-comm-sequence a b =
  funExt (cauchyProduct-comm a b)


cauchyProduct-addLeft : ∀ a b c n →
  cauchyProduct (λ k → a k + b k) c n ≡
  cauchyProduct a c n + cauchyProduct b c n
cauchyProduct-addLeft a b c n =
  partialSum-pointwise
    (λ k → (a k + b k) · c (n ∸ k))
    (λ k →
      a k · c (n ∸ k)
        + b k · c (n ∸ k))
    (λ k → mulDistL (a k) (b k) (c (n ∸ k)))
    (suc n)
  ∙ partialSum-add
      (λ k → a k · c (n ∸ k))
      (λ k → b k · c (n ∸ k))
      (suc n)


cauchyProduct-addRight : ∀ a b c n →
  cauchyProduct a (λ k → b k + c k) n ≡
  cauchyProduct a b n + cauchyProduct a c n
cauchyProduct-addRight a b c n =
  partialSum-pointwise
    (λ k → a k · (b (n ∸ k) + c (n ∸ k)))
    (λ k →
      a k · b (n ∸ k)
        + a k · c (n ∸ k))
    (λ k → mulDistR (a k) (b (n ∸ k)) (c (n ∸ k)))
    (suc n)
  ∙ partialSum-add
      (λ k → a k · b (n ∸ k))
      (λ k → a k · c (n ∸ k))
      (suc n)


cauchyProduct-zeroLeft : ∀ b n →
  cauchyProduct (λ _ → 0ℝ) b n ≡ 0ℝ
cauchyProduct-zeroLeft b n =
  partialSum-pointwise
    (λ k → 0ℝ · b (n ∸ k))
    (λ _ → 0ℝ)
    (λ k → ℝRing.0LeftAnnihilates (b (n ∸ k)))
    (suc n)
  ∙ partialSum-zeroSequence (suc n)


cauchyProduct-zeroRight : ∀ a n →
  cauchyProduct a (λ _ → 0ℝ) n ≡ 0ℝ
cauchyProduct-zeroRight a n =
  cauchyProduct-comm a (λ _ → 0ℝ) n
  ∙ cauchyProduct-zeroLeft a n


singletonSeries : ℝ → RealSequence
singletonSeries c zero = c
singletonSeries c (suc _) = 0ℝ


cauchyProduct-singleton-left : ∀ c b n →
  cauchyProduct (singletonSeries c) b n ≡
  scaleSeries c b n
cauchyProduct-singleton-left c b zero =
  cauchyProduct-zero (singletonSeries c) b
cauchyProduct-singleton-left c b (suc n) =
  cauchyProduct-left-step (singletonSeries c) b n
  ∙ cong (c · b (suc n) +_)
      (cauchyProduct-zeroLeft b n)
  ∙ addIdR (c · b (suc n))


cauchyProduct-singleton-right : ∀ a c n →
  cauchyProduct a (singletonSeries c) n ≡
  scaleSeries c a n
cauchyProduct-singleton-right a c n =
  cauchyProduct-comm a (singletonSeries c) n
  ∙ cauchyProduct-singleton-left c a n


unitSeries : RealSequence
unitSeries = singletonSeries 1ℝ


cauchyProduct-unitLeft : ∀ b n →
  cauchyProduct unitSeries b n ≡ b n
cauchyProduct-unitLeft b n =
  cauchyProduct-singleton-left 1ℝ b n
  ∙ mulIdL (b n)


cauchyProduct-unitRight : ∀ a n →
  cauchyProduct a unitSeries n ≡ a n
cauchyProduct-unitRight a n =
  cauchyProduct-singleton-right a 1ℝ n
  ∙ mulIdL (a n)


cauchyProduct-unitLeft-sequence : ∀ b →
  cauchyProduct unitSeries b ≡ b
cauchyProduct-unitLeft-sequence b =
  funExt (cauchyProduct-unitLeft b)


cauchyProduct-unitRight-sequence : ∀ a →
  cauchyProduct a unitSeries ≡ a
cauchyProduct-unitRight-sequence a =
  funExt (cauchyProduct-unitRight a)


partialSum-right-scale : ∀ terms c n →
  partialSum (λ k → terms k · c) n ≡
  partialSum terms n · c
partialSum-right-scale terms c n =
  partialSum-pointwise
    (λ k → terms k · c)
    (λ k → c · terms k)
    (λ k → mulComm (terms k) c)
    n
  ∙ partialSum-scale c terms n
  ∙ mulComm c (partialSum terms n)


rectangularSum :
  RealSequence → RealSequence → ℕ → ℕ → ℝ
rectangularSum a b m n =
  partialSum (λ i → a i · partialSum b n) m


rectangularSum-product : ∀ a b m n →
  rectangularSum a b m n ≡
  partialSum a m · partialSum b n
rectangularSum-product a b m n =
  partialSum-right-scale a (partialSum b n) m


cauchyProductTriangle :
  RealSequence → RealSequence → RealSequence
cauchyProductTriangle a b =
  triangularSum (λ i j → a i · b j)


cauchyProductTriangle-rows : ∀ a b n →
  cauchyProductTriangle a b n ≡
  partialSum
    (λ i → a i · partialSum b (n ∸ i)) n
cauchyProductTriangle-rows a b n =
  partialSum-pointwise
    (λ i →
      partialSum (λ j → a i · b j) (n ∸ i))
    (λ i → a i · partialSum b (n ∸ i))
    (λ i → partialSum-scale (a i) b (n ∸ i))
    n


partialSum-cauchyProduct : ∀ a b n →
  partialSum (cauchyProduct a b) n ≡
  cauchyProductTriangle a b n
partialSum-cauchyProduct a b n =
  partialSum-diagonalSum
    (λ i j → a i · b j) n


partialSum-cauchyProduct-rows : ∀ a b n →
  partialSum (cauchyProduct a b) n ≡
  partialSum
    (λ i → a i · partialSum b (n ∸ i)) n
partialSum-cauchyProduct-rows a b n =
  partialSum-cauchyProduct a b n
  ∙ cauchyProductTriangle-rows a b n


partialSum-cauchyProduct-sequence : ∀ a b →
  partialSum (cauchyProduct a b) ≡
  cauchyProductTriangle a b
partialSum-cauchyProduct-sequence a b =
  funExt (partialSum-cauchyProduct a b)


cauchyProductIsCauchyFromTriangle : ∀ a b →
  SeqWitness (cauchyProductTriangle a b) →
  IsCauchySeries (cauchyProduct a b)
cauchyProductIsCauchyFromTriangle a b =
  subst SeqWitness
    (sym (partialSum-cauchyProduct-sequence a b))


cauchyProductHasSumFromTriangle : ∀ a b value →
  isLimitSequence (cauchyProductTriangle a b) value →
  HasSum (cauchyProduct a b) value
cauchyProductHasSumFromTriangle a b value =
  subst (λ sequence → isLimitSequence sequence value)
    (sym (partialSum-cauchyProduct-sequence a b))


cauchyProductSummableFromTriangle : ∀ a b →
  SequenceLimit (cauchyProductTriangle a b) →
  Summable (cauchyProduct a b)
cauchyProductSummableFromTriangle a b
    (value , triangleLimit) =
  value
  , cauchyProductHasSumFromTriangle
      a b value triangleLimit


cauchyProductRemainder :
  RealSequence → RealSequence → RealSequence
cauchyProductRemainder a b n =
  partialSum
    (λ i →
      a i ·
        (partialSum b n - partialSum b (n ∸ i)))
    n


cauchyProductRemainderMajorant :
  RealSequence → RealSequence → ℕ → RealSequence
cauchyProductRemainderMajorant a b n i =
  absℝ (a i) ·
    absℝ (partialSum b n - partialSum b (n ∸ i))


cauchyProductRemainderAbsBound : ∀ a b n →
  absℝ (cauchyProductRemainder a b n) ≤ℝ
  partialSum (cauchyProductRemainderMajorant a b n) n
cauchyProductRemainderAbsBound a b n =
  subst
    (absℝ (cauchyProductRemainder a b n) ≤ℝ_)
    absoluteSummandsPath
    (partialSumAbsBound
      (λ i →
        a i ·
          (partialSum b n - partialSum b (n ∸ i)))
      n)
  where
  absoluteSummandsPath :
    partialSum
      (absℝ ∘
        (λ i →
          a i ·
            (partialSum b n - partialSum b (n ∸ i))))
      n ≡
    partialSum (cauchyProductRemainderMajorant a b n) n
  absoluteSummandsPath =
    partialSum-pointwise
      (absℝ ∘
        (λ i →
          a i ·
            (partialSum b n - partialSum b (n ∸ i))))
      (cauchyProductRemainderMajorant a b n)
      (λ i →
        absMul
          (a i)
          (partialSum b n - partialSum b (n ∸ i)))
      n


cauchyProductTriangle-plus-remainder : ∀ a b n →
  cauchyProductTriangle a b n
    + cauchyProductRemainder a b n ≡
  rectangularSum a b n n
cauchyProductTriangle-plus-remainder a b n =
  cong (_+ cauchyProductRemainder a b n)
    (cauchyProductTriangle-rows a b n)
  ∙ sym
      (partialSum-add
        (λ i → a i · partialSum b (n ∸ i))
        (λ i →
          a i ·
            (partialSum b n - partialSum b (n ∸ i)))
        n)
  ∙ partialSum-pointwise
      (λ i →
        a i · partialSum b (n ∸ i)
          + a i ·
              (partialSum b n - partialSum b (n ∸ i)))
      (λ i → a i · partialSum b n)
      summandPath n
  where
  summandPath : ∀ i →
    a i · partialSum b (n ∸ i)
      + a i ·
          (partialSum b n - partialSum b (n ∸ i)) ≡
    a i · partialSum b n
  summandPath i =
    sym
      (mulDistR
        (a i)
        (partialSum b (n ∸ i))
        (partialSum b n - partialSum b (n ∸ i)))
    ∙ cong (a i ·_)
        ( addComm
            (partialSum b (n ∸ i))
            (partialSum b n - partialSum b (n ∸ i))
        ∙ subAddCancel
            (partialSum b n) (partialSum b (n ∸ i))
        )


rectangularProduct-decomposition : ∀ a b n →
  partialSum a n · partialSum b n ≡
  partialSum (cauchyProduct a b) n
    + cauchyProductRemainder a b n
rectangularProduct-decomposition a b n =
  sym (rectangularSum-product a b n n)
  ∙ sym (cauchyProductTriangle-plus-remainder a b n)
  ∙ cong (_+ cauchyProductRemainder a b n)
      (sym (partialSum-cauchyProduct a b n))


partialSum-cauchyProduct-as-rectangle-minus-remainder : ∀ a b n →
  partialSum (cauchyProduct a b) n ≡
  partialSum a n · partialSum b n
    - cauchyProductRemainder a b n
partialSum-cauchyProduct-as-rectangle-minus-remainder a b n =
  sym
    ( cong
        (_- cauchyProductRemainder a b n)
        (rectangularProduct-decomposition a b n)
    ∙ addSubCancel
        (partialSum (cauchyProduct a b) n)
        (cauchyProductRemainder a b n)
    )


cauchyProductHasSumWithRemainderLimit : ∀ a b aSum bSum →
  HasSum a aSum →
  HasSum b bSum →
  isLimitSequence (cauchyProductRemainder a b) 0ℝ →
  HasSum (cauchyProduct a b) (aSum · bSum)
cauchyProductHasSumWithRemainderLimit
    a b aSum bSum aHasSum bHasSum remainderLimit =
  subst
    (λ sequence → isLimitSequence sequence (aSum · bSum))
    (sym (funExt
      (partialSum-cauchyProduct-as-rectangle-minus-remainder
        a b)))
    differenceLimit
  where
  differenceLimit :
    isLimitSequence
      (λ n →
        partialSum a n · partialSum b n
          - cauchyProductRemainder a b n)
      (aSum · bSum)
  differenceLimit =
    subst
      (isLimitSequence
        (λ n →
          partialSum a n · partialSum b n
            - cauchyProductRemainder a b n))
      (subZero (aSum · bSum))
      (subPresIsLimitSequence
        (mulPresIsLimitSequence aHasSum bHasSum)
        remainderLimit)


cauchyProductSummableWithRemainderLimit : ∀ a b →
  (aSummable : Summable a) →
  (bSummable : Summable b) →
  isLimitSequence (cauchyProductRemainder a b) 0ℝ →
  Summable (cauchyProduct a b)
cauchyProductSummableWithRemainderLimit
    a b aSummable bSummable remainderLimit =
  seriesSum a aSummable · seriesSum b bSummable
  , cauchyProductHasSumWithRemainderLimit
      a b
      (seriesSum a aSummable)
      (seriesSum b bSummable)
      (seriesSumHasSum a aSummable)
      (seriesSumHasSum b bSummable)
      remainderLimit


seriesSum-cauchyProductWithRemainderLimit : ∀ a b →
  (aSummable : Summable a) →
  (bSummable : Summable b) →
  (productSummable : Summable (cauchyProduct a b)) →
  (remainderLimit :
    isLimitSequence (cauchyProductRemainder a b) 0ℝ) →
  seriesSum (cauchyProduct a b) productSummable ≡
  seriesSum a aSummable · seriesSum b bSummable
seriesSum-cauchyProductWithRemainderLimit
    a b aSummable bSummable
    productSummable remainderLimit =
  seriesSumIndependent
    (cauchyProduct a b) productSummable
    (cauchyProductSummableWithRemainderLimit
      a b aSummable bSummable remainderLimit)


absoluteCauchyProduct :
  RealSequence → RealSequence → RealSequence
absoluteCauchyProduct a b =
  cauchyProduct (absℝ ∘ a) (absℝ ∘ b)


cauchyProductAbsBound : ∀ a b n →
  absℝ (cauchyProduct a b n) ≤ℝ
  absoluteCauchyProduct a b n
cauchyProductAbsBound a b n =
  subst
    (absℝ (cauchyProduct a b n) ≤ℝ_)
    absoluteSummandsPath
    (partialSumAbsBound
      (λ k → a k · b (n ∸ k)) (suc n))
  where
  absoluteSummandsPath :
    partialSum
      (absℝ ∘ (λ k → a k · b (n ∸ k)))
      (suc n) ≡
    absoluteCauchyProduct a b n
  absoluteSummandsPath =
    partialSum-pointwise
      (absℝ ∘ (λ k → a k · b (n ∸ k)))
      (λ k → absℝ (a k) · absℝ (b (n ∸ k)))
      (λ k → absMul (a k) (b (n ∸ k)))
      (suc n)


absoluteCauchyProductFromMajorant : ∀ a b →
  IsCauchySeries (absoluteCauchyProduct a b) →
  IsAbsolutelyCauchySeries (cauchyProduct a b)
absoluteCauchyProductFromMajorant
    a b absoluteProductCauchy =
  dominatedCauchySeriesIsCauchy
    (absℝ ∘ cauchyProduct a b)
    (absoluteCauchyProduct a b)
    dominates absoluteProductCauchy
  where
  dominates : ∀ n →
    absℝ (absℝ (cauchyProduct a b n)) ≤ℝ
    absoluteCauchyProduct a b n
  dominates n =
    subst
      (_≤ℝ absoluteCauchyProduct a b n)
      (sym (absIdem (cauchyProduct a b n)))
      (cauchyProductAbsBound a b n)

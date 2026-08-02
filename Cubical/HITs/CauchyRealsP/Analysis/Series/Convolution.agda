module Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc ; _∸_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import
  Cubical.HITs.CauchyRealsP.Analysis.Sequence.Cauchy
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations

partialSum-first : ∀ terms n →
  partialSum terms (suc n) ≡
  terms zero + partialSum (terms ∘ suc) n
partialSum-first terms zero =
  addIdL (terms zero)
  ∙ sym (addIdR (terms zero))
partialSum-first terms (suc n) =
  cong (_+ terms (suc n))
    (partialSum-first terms n)
  ∙ sym
      (addAssoc
      (terms zero)
      (partialSum (terms ∘ suc) n)
      (terms (suc n)))

boundedSubtractInvolutive :
  ∀ k n →
  k ℕ.≤ n →
  k ≡ n ∸ (n ∸ k)
boundedSubtractInvolutive k n k≤n =
  ℕ.inj-+m
    ( ℕ.+-comm k (n ∸ k)
    ∙ ℕ.[n-m]+m k n k≤n
    ∙ sym
        (ℕ.[n-m]+m
          (n ∸ k) n
          (ℕ.∸-≤ n k))
    )

partialSum-reverse : ∀ terms n →
  partialSum terms (suc n) ≡
  partialSum
    (λ k → terms (n ∸ k))
    (suc n)
partialSum-reverse terms zero =
  refl
partialSum-reverse terms (suc n) =
  cong (_+ terms (suc n))
    (partialSum-reverse terms n)
  ∙ addComm
      (partialSum
        (λ k → terms (n ∸ k))
        (suc n))
      (terms (suc n))
  ∙ sym
      (partialSum-first
        (λ k → terms (suc n ∸ k))
        (suc n))

partialSum-right-scale : ∀ terms c n →
  partialSum (λ k → terms k · c) n ≡
  partialSum terms n · c
partialSum-right-scale terms c zero =
  sym (mulZeroL c)
partialSum-right-scale terms c (suc n) =
  cong (_+ (terms n · c))
    (partialSum-right-scale terms c n)
  ∙ sym
      (mulDistL
        (partialSum terms n)
        (terms n)
        c)

rectangularSum :
  RealSequence → RealSequence → ℕ → ℕ → ℝ
rectangularSum a b m n =
  partialSum
    (λ i → a i · partialSum b n)
    m

rectangularSum-product : ∀ a b m n →
  rectangularSum a b m n ≡
  partialSum a m · partialSum b n
rectangularSum-product a b m n =
  partialSum-right-scale
    a (partialSum b n) m

cauchyProduct :
  RealSequence → RealSequence → RealSequence
cauchyProduct a b n =
  partialSum
    (λ k → a k · b (n ∸ k))
    (suc n)

cauchyProduct-zero : ∀ a b →
  cauchyProduct a b zero ≡
  a zero · b zero
cauchyProduct-zero a b =
  addIdL (a zero · b zero)

cauchyProduct-comm : ∀ a b n →
  cauchyProduct a b n ≡
  cauchyProduct b a n
cauchyProduct-comm a b n =
  partialSum-reverse
    (λ k → a k · b (n ∸ k))
    n
  ∙ partialSum-pointwiseBefore
      (λ k →
        a (n ∸ k)
          · b (n ∸ (n ∸ k)))
      (λ k →
        b k · a (n ∸ k))
      (suc n)
      summand-path
  where
  summand-path : ∀ k →
    k ℕ.< suc n →
    a (n ∸ k)
      · b (n ∸ (n ∸ k))
      ≡
    b k · a (n ∸ k)
  summand-path k k<sucn =
    cong
      (a (n ∸ k) ·_)
      (cong b
        (sym
          (boundedSubtractInvolutive
            k n
            (ℕ.pred-≤-pred k<sucn))))
    ∙ mulComm
        (a (n ∸ k))
        (b k)

cauchyProduct-comm-sequence : ∀ a b →
  cauchyProduct a b ≡
  cauchyProduct b a
cauchyProduct-comm-sequence a b =
  funExt (cauchyProduct-comm a b)

cauchyProduct-left-step : ∀ a b n →
  cauchyProduct a b (suc n) ≡
  a zero · b (suc n)
    + cauchyProduct (a ∘ suc) b n
cauchyProduct-left-step a b n =
  partialSum-first
    (λ k → a k · b (suc n ∸ k))
    (suc n)

singletonSeries : ℝ → RealSequence
singletonSeries c zero =
  c
singletonSeries c (suc _) =
  0

partialSum-singletonSeries : ∀ c n →
  partialSum (singletonSeries c) (suc n) ≡ c
partialSum-singletonSeries c zero =
  addIdL c
partialSum-singletonSeries c (suc n) =
  cong (_+ 0)
    (partialSum-singletonSeries c n)
  ∙ addIdR c

cauchyProduct-zeroLeft : ∀ b n →
  cauchyProduct (λ _ → 0) b n ≡ 0
cauchyProduct-zeroLeft b n =
  partialSum-pointwise
    (λ k → 0 · b (n ∸ k))
    (λ _ → 0)
    (λ k → mulZeroL (b (n ∸ k)))
    (suc n)
  ∙ partialSum-zeroSequence (suc n)

cauchyProduct-singleton-left : ∀ c b n →
  cauchyProduct (singletonSeries c) b n ≡
  scaleSeries c b n
cauchyProduct-singleton-left c b zero =
  cauchyProduct-zero
    (singletonSeries c) b
cauchyProduct-singleton-left c b (suc n) =
  cauchyProduct-left-step
    (singletonSeries c) b n
  ∙ cong
      (c · b (suc n) +_)
      (cauchyProduct-zeroLeft b n)
  ∙ addIdR (c · b (suc n))

triangularRows :
  RealSequence → RealSequence → ℕ → ℝ
triangularRows a b n =
  partialSum
    (λ i → a i · partialSum b (n ∸ i))
    n

triangularRows-step : ∀ a b n →
  triangularRows a b (suc n) ≡
  triangularRows a b n
    + cauchyProduct a b n
triangularRows-step a b zero =
  cong
      (λ x → 0 + a zero · x)
      (addIdL (b zero))
  ∙ addIdL (a zero · b zero)
  ∙ sym (addIdL (a zero · b zero))
  ∙ cong
      (0 +_)
      (sym (cauchyProduct-zero a b))
triangularRows-step a b (suc n) =
  partialSum-first
    (λ i →
      a i · partialSum b (suc (suc n) ∸ i))
    (suc n)
  ∙ cong
      (a zero · partialSum b (suc (suc n)) +_)
      (triangularRows-step (a ∘ suc) b n)
  ∙ cong
      (_+
        ( triangularRows (a ∘ suc) b n
        + cauchyProduct (a ∘ suc) b n
        ))
      (mulDistR
        (a zero)
        (partialSum b (suc n))
        (b (suc n)))
  ∙ interchange
  ∙ cong₂ _+_
      (sym
        (partialSum-first
          (λ i →
            a i · partialSum b (suc n ∸ i))
          n))
      (sym
        (cauchyProduct-left-step
          a b n))
  where
  interchange :
    a zero · partialSum b (suc n)
      + a zero · b (suc n)
      + ( triangularRows (a ∘ suc) b n
        + cauchyProduct (a ∘ suc) b n
        )
      ≡
    ( a zero · partialSum b (suc n)
      + triangularRows (a ∘ suc) b n
      )
      +
    ( a zero · b (suc n)
      + cauchyProduct (a ∘ suc) b n
      )
  interchange =
    sym
      (addAssoc
        (a zero · partialSum b (suc n))
        (a zero · b (suc n))
        ( triangularRows (a ∘ suc) b n
        + cauchyProduct (a ∘ suc) b n
        ))
    ∙ cong
        (a zero · partialSum b (suc n) +_)
        ( addAssoc
            (a zero · b (suc n))
            (triangularRows (a ∘ suc) b n)
            (cauchyProduct (a ∘ suc) b n)
        ∙ cong
            (_+
              cauchyProduct (a ∘ suc) b n)
            (addComm
              (a zero · b (suc n))
              (triangularRows (a ∘ suc) b n))
        ∙ sym
            (addAssoc
              (triangularRows (a ∘ suc) b n)
              (a zero · b (suc n))
              (cauchyProduct (a ∘ suc) b n))
        )
    ∙ addAssoc
        (a zero · partialSum b (suc n))
        (triangularRows (a ∘ suc) b n)
        ( a zero · b (suc n)
        + cauchyProduct (a ∘ suc) b n
        )

partialSum-cauchyProduct : ∀ a b n →
  partialSum (cauchyProduct a b) n ≡
  triangularRows a b n
partialSum-cauchyProduct a b zero =
  refl
partialSum-cauchyProduct a b (suc n) =
  cong (_+ cauchyProduct a b n)
    (partialSum-cauchyProduct a b n)
  ∙ sym
      (triangularRows-step a b n)

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
    absoluteSummands≡positiveSummands
    (partialSumAbsBound
      (λ k → a k · b (n ∸ k))
      (suc n))
  where
  absoluteSummands≡positiveSummands :
    partialSum
      (absℝ ∘
        (λ k → a k · b (n ∸ k)))
      (suc n)
      ≡
    absoluteCauchyProduct a b n
  absoluteSummands≡positiveSummands =
    partialSum-pointwise
      (absℝ ∘
        (λ k → a k · b (n ∸ k)))
      (λ k →
        absℝ (a k) · absℝ (b (n ∸ k)))
      (λ k → absMul (a k) (b (n ∸ k)))
      (suc n)

absoluteCauchyProductFromMajorant :
  ∀ a b →
  IsCauchySeries (absoluteCauchyProduct a b) →
  IsAbsolutelyCauchySeries (cauchyProduct a b)
absoluteCauchyProductFromMajorant
  a b positive-product-cauchy =
    dominatedCauchySeriesIsCauchy
      (absℝ ∘ cauchyProduct a b)
      (absoluteCauchyProduct a b)
      dominates
      positive-product-cauchy
  where
  dominates : ∀ n →
    absℝ (absℝ (cauchyProduct a b n)) ≤ℝ
    absoluteCauchyProduct a b n
  dominates n =
    subst
      (_≤ℝ absoluteCauchyProduct a b n)
      (sym
        (absIdem (cauchyProduct a b n)))
      (cauchyProductAbsBound a b n)

CauchyProductRectangularApproximation :
  RealSequence → RealSequence → Type
CauchyProductRectangularApproximation a b =
  AsymptoticallyCloseSeq
    (λ n →
      partialSum a n · partialSum b n)
    (partialSum (cauchyProduct a b))

singletonRectangularPartialSums : ∀ c b n →
  partialSum (singletonSeries c) n
    · partialSum b n
    ≡
  partialSum
    (cauchyProduct (singletonSeries c) b) n
singletonRectangularPartialSums c b zero =
  mulZeroL 0
singletonRectangularPartialSums c b (suc n) =
  cong
      (_· partialSum b (suc n))
      (partialSum-singletonSeries c n)
  ∙ sym
      (partialSum-scale c b (suc n))
  ∙ sym
      (partialSum-pointwise
        (cauchyProduct (singletonSeries c) b)
        (scaleSeries c b)
        (cauchyProduct-singleton-left c b)
        (suc n))

singletonRectangularApproximation : ∀ c b →
  CauchyProductRectangularApproximation
    (singletonSeries c) b
singletonRectangularApproximation c b ε =
  0
  , λ n _ →
      subst
        (_∼[ ε ]
          partialSum
            (cauchyProduct (singletonSeries c) b)
            n)
        (sym
          (singletonRectangularPartialSums
            c b n))
        (refl∼
          (partialSum
            (cauchyProduct (singletonSeries c) b)
            n)
          ε)

cauchyProductRemainder :
  RealSequence → RealSequence → RealSequence
cauchyProductRemainder a b n =
  partialSum
    (λ i →
      a i ·
        ( partialSum b n
        - partialSum b (n ∸ i)
        ))
    n

cauchyProductRemainderMajorant :
  RealSequence → RealSequence → ℕ → RealSequence
cauchyProductRemainderMajorant a b n i =
  absℝ (a i)
    · absℝ
        ( partialSum b n
        - partialSum b (n ∸ i)
        )

cauchyProductRemainderAbsBound : ∀ a b n →
  absℝ (cauchyProductRemainder a b n)
    ≤ℝ
  partialSum
    (cauchyProductRemainderMajorant a b n)
    n
cauchyProductRemainderAbsBound a b n =
  subst
    (absℝ (cauchyProductRemainder a b n) ≤ℝ_)
    absoluteSummands≡majorant
    (partialSumAbsBound
      (λ i →
        a i ·
          ( partialSum b n
          - partialSum b (n ∸ i)
          ))
      n)
  where
  absoluteSummands≡majorant :
    partialSum
      (absℝ ∘
        (λ i →
          a i ·
            ( partialSum b n
            - partialSum b (n ∸ i)
            )))
      n
      ≡
    partialSum
      (cauchyProductRemainderMajorant a b n)
      n
  absoluteSummands≡majorant =
    partialSum-pointwise
      (absℝ ∘
        (λ i →
          a i ·
            ( partialSum b n
            - partialSum b (n ∸ i)
            )))
      (cauchyProductRemainderMajorant a b n)
      (λ i →
        absMul
          (a i)
          ( partialSum b n
          - partialSum b (n ∸ i)
          ))
      n

triangularRows-plus-remainder : ∀ a b n →
  triangularRows a b n
    + cauchyProductRemainder a b n
    ≡
  rectangularSum a b n n
triangularRows-plus-remainder a b n =
  sym
    (partialSum-add
      (λ i →
        a i · partialSum b (n ∸ i))
      (λ i →
        a i ·
          ( partialSum b n
          - partialSum b (n ∸ i)
          ))
      n)
  ∙ partialSum-pointwise
      (λ i →
        a i · partialSum b (n ∸ i)
        +
        a i ·
          ( partialSum b n
          - partialSum b (n ∸ i)
          ))
      (λ i → a i · partialSum b n)
      summand-path
      n
  where
  summand-path : ∀ i →
    a i · partialSum b (n ∸ i)
      +
    a i ·
      ( partialSum b n
      - partialSum b (n ∸ i)
      )
      ≡
    a i · partialSum b n
  summand-path i =
    sym
      (mulDistR
        (a i)
        (partialSum b (n ∸ i))
        ( partialSum b n
        - partialSum b (n ∸ i)
        ))
    ∙ cong
        (a i ·_)
        ( addComm
            (partialSum b (n ∸ i))
            ( partialSum b n
            - partialSum b (n ∸ i)
            )
        ∙ subAddCancel
            (partialSum b n)
            (partialSum b (n ∸ i))
        )

rectangularProduct-decomposition : ∀ a b n →
  partialSum a n · partialSum b n
    ≡
  partialSum (cauchyProduct a b) n
    + cauchyProductRemainder a b n
rectangularProduct-decomposition a b n =
  sym (rectangularSum-product a b n n)
  ∙ sym (triangularRows-plus-remainder a b n)
  ∙ cong
      (_+ cauchyProductRemainder a b n)
      (sym
        (partialSum-cauchyProduct a b n))

CauchyProductRemainderVanishes :
  RealSequence → RealSequence → Type
CauchyProductRemainderVanishes a b =
  AsymptoticallyCloseSeq
    (cauchyProductRemainder a b)
    (λ _ → 0)

CauchyProductRemainderModulus :
  RealSequence → RealSequence → Type
CauchyProductRemainderModulus a b =
  Σ[ modulus ∈ (ℚ₊ → ℕ) ]
    (∀ ε n →
      modulus ε ℕ.≤ n →
      absℝ (cauchyProductRemainder a b n)
        <ℝ rat (fst ε))

remainderModulus→remainderVanishes :
  ∀ a b →
  CauchyProductRemainderModulus a b →
  CauchyProductRemainderVanishes a b
remainderModulus→remainderVanishes
  a b (modulus , bound) ε =
    modulus ε
    , λ n modulus≤n →
        absDifference<→closeness
          (cauchyProductRemainder a b n)
          0 ε
          (subst
            (_<ℝ rat (fst ε))
            (sym
              ( cong absℝ
                  (subZeroR
                    (cauchyProductRemainder
                      a b n))
              ))
            (bound ε n modulus≤n))

remainderVanishes→remainderModulus :
  ∀ a b →
  CauchyProductRemainderVanishes a b →
  CauchyProductRemainderModulus a b
remainderVanishes→remainderModulus
  a b remainder-vanishes .fst ε =
    fst (remainder-vanishes ε)
remainderVanishes→remainderModulus
  a b remainder-vanishes
  .snd ε n modulus≤n =
    subst
      (_<ℝ rat (fst ε))
      (cong absℝ
        (subZeroR
          (cauchyProductRemainder a b n)))
      (closeness→absDifference<
        (cauchyProductRemainder a b n)
        0 ε
        (snd (remainder-vanishes ε)
          n modulus≤n))

remainderVanishes→rectangularApproximation :
  ∀ a b →
  CauchyProductRemainderVanishes a b →
  CauchyProductRectangularApproximation a b
remainderVanishes→rectangularApproximation
  a b remainder-vanishes ε =
    fst (remainder-vanishes ε)
    , λ n modulus≤n →
        subst2 (_∼[ ε ]_)
          (sym
            (rectangularProduct-decomposition
              a b n))
          (addIdR
            (partialSum
              (cauchyProduct a b) n))
          (addPres∼₂
            (partialSum (cauchyProduct a b) n)
            (cauchyProductRemainder a b n)
            0 ε
            (snd (remainder-vanishes ε)
              n modulus≤n))

rectangularApproximation→remainderVanishes :
  ∀ a b →
  CauchyProductRectangularApproximation a b →
  CauchyProductRemainderVanishes a b
rectangularApproximation→remainderVanishes
  a b approximation ε =
    fst (approximation ε)
    , λ n modulus≤n →
        subst2 (_∼[ ε ]_)
          (remainder-path n)
          (subSelf
            (partialSum (cauchyProduct a b) n))
          (addPres∼₁
            (partialSum a n · partialSum b n)
            (partialSum (cauchyProduct a b) n)
            (- partialSum (cauchyProduct a b) n)
            ε
            (snd (approximation ε)
              n modulus≤n))
  where
  remainder-path : ∀ n →
    partialSum a n · partialSum b n
      - partialSum (cauchyProduct a b) n
      ≡
    cauchyProductRemainder a b n
  remainder-path n =
    cong
      (_- partialSum (cauchyProduct a b) n)
      (rectangularProduct-decomposition a b n)
    ∙ cong
        (_- partialSum (cauchyProduct a b) n)
        (addComm
          (partialSum (cauchyProduct a b) n)
          (cauchyProductRemainder a b n))
    ∙ addSubCancel
        (cauchyProductRemainder a b n)
        (partialSum (cauchyProduct a b) n)

UniformPartialSumAbsBound :
  ℚ₊ → RealSequence → Type
UniformPartialSumAbsBound B terms =
  ∀ n →
  absℝ (partialSum terms n)
    ≤ℝ rat (fst B)

UniformAbsolutePartialSumBound :
  ℚ₊ → RealSequence → Type
UniformAbsolutePartialSumBound B terms =
  ∀ n →
  partialSum (absℝ ∘ terms) n
    ≤ℝ rat (fst B)

uniformAbsoluteBound→uniformBound :
  ∀ B terms →
  UniformAbsolutePartialSumBound B terms →
  UniformPartialSumAbsBound B terms
uniformAbsoluteBound→uniformBound
  B terms absolute-bounded n =
    ≤ℝ-trans
      (absℝ (partialSum terms n))
      (partialSum (absℝ ∘ terms) n)
      (rat (fst B))
      (partialSumAbsBound terms n)
      (absolute-bounded n)

cauchyProductIsCauchy :
  ∀ B a b →
  UniformPartialSumAbsBound B a →
  UniformPartialSumAbsBound B b →
  IsCauchySeries a →
  IsCauchySeries b →
  CauchyProductRectangularApproximation a b →
  IsCauchySeries (cauchyProduct a b)
cauchyProductIsCauchy
  B a b a-bounded b-bounded
  a-cauchy b-cauchy approximation =
    asymptoticallyCloseSeqPresIsCauchySeq
      rectangularPartialSums
      (partialSum (cauchyProduct a b))
      approximation
      rectangularPartialSumsCauchy
  where
  rectangularPartialSums : RealSequence
  rectangularPartialSums n =
    partialSum a n · partialSum b n

  rectangularPartialSumsCauchy :
    isCauchySeq rectangularPartialSums
  rectangularPartialSumsCauchy =
    boundedMulPresIsCauchySeq
      B
      (partialSum a)
      (partialSum b)
      a-bounded b-bounded
      a-cauchy b-cauchy

cauchyProductIsCauchyWithRemainderModulus :
  ∀ B a b →
  UniformPartialSumAbsBound B a →
  UniformPartialSumAbsBound B b →
  IsCauchySeries a →
  IsCauchySeries b →
  CauchyProductRemainderModulus a b →
  IsCauchySeries (cauchyProduct a b)
cauchyProductIsCauchyWithRemainderModulus
  B a b a-bounded b-bounded
  a-cauchy b-cauchy remainder-modulus =
    cauchyProductIsCauchy
      B a b
      a-bounded b-bounded
      a-cauchy b-cauchy
      (remainderVanishes→rectangularApproximation
        a b
        (remainderModulus→remainderVanishes
          a b remainder-modulus))

cauchyProductHasSum :
  ∀ a b a-sum b-sum →
  HasSum a a-sum →
  HasSum b b-sum →
  CauchyProductRectangularApproximation a b →
  HasSum (cauchyProduct a b) (a-sum · b-sum)
cauchyProductHasSum
  a b a-sum b-sum
  a-has-sum b-has-sum approximation =
    asymptoticallyCloseSeqPresIsLimitSeq
      rectangularPartialSums
      (partialSum (cauchyProduct a b))
      (a-sum · b-sum)
      approximation
      rectangularLimit
  where
  rectangularPartialSums : RealSequence
  rectangularPartialSums n =
    partialSum a n · partialSum b n

  rectangularLimit :
    isLimitSeq rectangularPartialSums
      (a-sum · b-sum)
  rectangularLimit =
    mulPresIsLimitSeq
      (partialSum a)
      (partialSum b)
      a-sum b-sum
      a-has-sum b-has-sum

cauchyProductSummable :
  ∀ a b →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  CauchyProductRectangularApproximation a b →
  Summable (cauchyProduct a b)
cauchyProductSummable
  a b a-summable b-summable approximation =
    seriesSum a a-summable
      · seriesSum b b-summable
    , cauchyProductHasSum
        a b
        (seriesSum a a-summable)
        (seriesSum b b-summable)
        (seriesSumHasSum a a-summable)
        (seriesSumHasSum b b-summable)
        approximation

cauchyProductSummableWithRemainderModulus :
  ∀ a b →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  CauchyProductRemainderModulus a b →
  Summable (cauchyProduct a b)
cauchyProductSummableWithRemainderModulus
  a b a-summable b-summable
  remainder-modulus =
    cauchyProductSummable
      a b a-summable b-summable
      (remainderVanishes→rectangularApproximation
        a b
        (remainderModulus→remainderVanishes
          a b remainder-modulus))

seriesSum-cauchyProduct :
  ∀ a b
  (a-summable : Summable a)
  (b-summable : Summable b)
  (product-summable :
    Summable (cauchyProduct a b)) →
  CauchyProductRectangularApproximation a b →
  seriesSum (cauchyProduct a b)
      product-summable
    ≡
  seriesSum a a-summable
    · seriesSum b b-summable
seriesSum-cauchyProduct
  a b a-summable b-summable
  product-summable approximation =
    seriesSumIndependent
      (cauchyProduct a b)
      product-summable
      (cauchyProductSummable
        a b a-summable b-summable
        approximation)

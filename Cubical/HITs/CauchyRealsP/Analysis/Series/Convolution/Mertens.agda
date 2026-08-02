module Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution.Mertens where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc ; _∸_)
  renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.Data.Rationals.Inverse

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
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution

remainingIndexAbove :
  ∀ minimum split n i →
  i ℕ.< split →
  minimum +ℕ split ℕ.≤ n →
  minimum ℕ.≤ n ∸ i
remainingIndexAbove minimum split n i i<split combined≤n =
  subst
    (λ k → k ℕ.≤ n ∸ i)
    (ℕ.+∸ minimum i)
    (ℕ.≤-∸-≤
      (minimum +ℕ i) n i
      (ℕ.≤-trans
        (ℕ.≤-k+
          (ℕ.<-weaken i<split))
        combined≤n))

partialSum-splitAt :
  ∀ terms split n →
  split ℕ.≤ n →
  partialSum terms n ≡
  partialSum terms split
    + partialSum
        (dropSeries split terms)
        (n ∸ split)
partialSum-splitAt terms split n split≤n =
  subst
    (λ k →
      partialSum terms k ≡
      partialSum terms split
        + partialSum
            (dropSeries split terms)
            (n ∸ split))
    (ℕ.[n-m]+m split n split≤n)
    (partialSum-drop-recombine
      split terms (n ∸ split))

absolutePartialSumLeSeriesSum :
  ∀ terms →
  (absolute-summable :
    AbsolutelySummable terms) →
  ∀ n →
  partialSum (absℝ ∘ terms) n
    ≤ℝ
  seriesSum (absℝ ∘ terms)
    absolute-summable
absolutePartialSumLeSeriesSum
  terms absolute-summable n =
    eventuallyLeSeqPresLimit
      (λ _ →
        partialSum (absℝ ∘ terms) n)
      (partialSum (absℝ ∘ terms))
      (partialSum (absℝ ∘ terms) n)
      (seriesSum
        (absℝ ∘ terms)
        absolute-summable)
      ( n
      , λ k n≤k →
          partialSumIndexMono
            (absℝ ∘ terms)
            (λ i → absNonnegative (terms i))
            n k n≤k
      )
      (constantIsLimitSeq
        (partialSum (absℝ ∘ terms) n))
      (seriesSumHasSum
        (absℝ ∘ terms)
        absolute-summable)

absoluteSeriesSumBound→uniformAbsoluteBound :
  ∀ B terms →
  (absolute-summable :
    AbsolutelySummable terms) →
  seriesSum (absℝ ∘ terms)
      absolute-summable
    ≤ℝ rat (fst B) →
  UniformAbsolutePartialSumBound B terms
absoluteSeriesSumBound→uniformAbsoluteBound
  B terms absolute-summable sum-bounded n =
    ≤ℝ-trans
      (partialSum (absℝ ∘ terms) n)
      (seriesSum
        (absℝ ∘ terms)
        absolute-summable)
      (rat (fst B))
      (absolutePartialSumLeSeriesSum
        terms absolute-summable n)
      sum-bounded

AbsoluteCauchySeriesSumBound :
  ℚ₊ → (terms : RealSequence) →
  IsAbsolutelyCauchySeries terms →
  Type
AbsoluteCauchySeriesSumBound
  B terms absolute =
    seriesSum (absℝ ∘ terms)
      (absoluteCauchySeriesIsAbsolutelySummable
        terms absolute)
      ≤ℝ
    rat (fst B)

absoluteCauchySumBound→uniformAbsoluteBound :
  ∀ B terms absolute →
  AbsoluteCauchySeriesSumBound
    B terms absolute →
  UniformAbsolutePartialSumBound B terms
absoluteCauchySumBound→uniformAbsoluteBound
  B terms absolute =
    absoluteSeriesSumBound→uniformAbsoluteBound
      B terms
      (absoluteCauchySeriesIsAbsolutelySummable
        terms absolute)

module _
  (A B : ℚ₊)
  (a b : RealSequence)
  (a-absolute-bounded :
    UniformAbsolutePartialSumBound A a)
  (b-bounded :
    UniformPartialSumAbsBound B b)
  (a-absolute-cauchy :
    IsAbsolutelyCauchySeries a)
  (b-cauchy :
    IsCauchySeries b)
  where

  doubleB : ℚ₊
  doubleB =
    B +₊ B

  prefixRadius : ℚ₊ → ℚ₊
  prefixRadius ε =
    (ε /4₊) ₊／₊ A

  tailRadius : ℚ₊ → ℚ₊
  tailRadius ε =
    (ε /4₊) ₊／₊ doubleB

  prefixLength : ℚ₊ → ℕ
  prefixLength ε =
    fst a-absolute-cauchy
      (tailRadius ε)

  separationLength : ℚ₊ → ℕ
  separationLength ε =
    fst b-cauchy
      (prefixRadius ε)

  mertensModulus : ℚ₊ → ℕ
  mertensModulus ε =
    separationLength ε
      +ℕ prefixLength ε

  prefixDifferenceBound :
    ∀ ε n i →
    i ℕ.< prefixLength ε →
    mertensModulus ε ℕ.≤ n →
    absℝ
      ( partialSum b n
      - partialSum b (n ∸ i)
      )
      ≤ℝ
    rat (fst (prefixRadius ε))
  prefixDifferenceBound
    ε n i i<prefix modulus≤n =
      <ℝ-weaken
        (absℝ
          ( partialSum b n
          - partialSum b (n ∸ i)
          ))
        (rat (fst (prefixRadius ε)))
        (closeness→absDifference<
          (partialSum b n)
          (partialSum b (n ∸ i))
          (prefixRadius ε)
          (snd b-cauchy
            (prefixRadius ε)
            n (n ∸ i)
            separation≤n
            separation≤remaining))
    where
    separation≤n :
      separationLength ε ℕ.≤ n
    separation≤n =
      ℕ.≤-trans
        ℕ.≤SumLeft
        modulus≤n

    separation≤remaining :
      separationLength ε ℕ.≤ n ∸ i
    separation≤remaining =
      remainingIndexAbove
        (separationLength ε)
        (prefixLength ε)
        n i i<prefix modulus≤n

  prefixTermBound :
    ∀ ε n i →
    i ℕ.< prefixLength ε →
    mertensModulus ε ℕ.≤ n →
    cauchyProductRemainderMajorant a b n i
      ≤ℝ
    absℝ (a i)
      · rat (fst (prefixRadius ε))
  prefixTermBound
    ε n i i<prefix modulus≤n =
      mulMonoL≤
        (absℝ
          ( partialSum b n
          - partialSum b (n ∸ i)
          ))
        (rat (fst (prefixRadius ε)))
        (absℝ (a i))
        (absNonnegative (a i))
        (prefixDifferenceBound
          ε n i i<prefix modulus≤n)

  prefixMajorantBound :
    ∀ ε n →
    mertensModulus ε ℕ.≤ n →
    partialSum
      (cauchyProductRemainderMajorant a b n)
      (prefixLength ε)
      ≤ℝ
    rat (fst (ε /4₊))
  prefixMajorantBound ε n modulus≤n =
    ≤ℝ-trans
      (partialSum
        (cauchyProductRemainderMajorant a b n)
        (prefixLength ε))
      (partialSum
        (λ i →
          absℝ (a i)
            · rat (fst (prefixRadius ε)))
        (prefixLength ε))
      (rat (fst (ε /4₊)))
      (partialSumMonoBefore
        (cauchyProductRemainderMajorant a b n)
        (λ i →
          absℝ (a i)
            · rat (fst (prefixRadius ε)))
        (prefixLength ε)
        (λ i i<prefix →
          prefixTermBound
            ε n i i<prefix modulus≤n))
      scaledPrefixBound
    where
    radiusNonnegative :
      0 ≤ℝ rat (fst (prefixRadius ε))
    radiusNonnegative =
      ≤ℚ→≤ℝ
        0 (fst (prefixRadius ε))
        (ℚ.<Weaken≤
          0 (fst (prefixRadius ε))
          (snd (prefixRadius ε)))

    productBound :
      partialSum (absℝ ∘ a)
          (prefixLength ε)
        · rat (fst (prefixRadius ε))
        ≤ℝ
      rat (fst A)
        · rat (fst (prefixRadius ε))
    productBound =
      mulMonoR≤
        (partialSum (absℝ ∘ a)
          (prefixLength ε))
        (rat (fst A))
        (rat (fst (prefixRadius ε)))
        radiusNonnegative
        (a-absolute-bounded
          (prefixLength ε))

    rationalProductPath :
      rat (fst A)
        · rat (fst (prefixRadius ε))
        ≡
      rat (fst (ε /4₊))
    rationalProductPath =
      mul-rat
        (fst A)
        (fst (prefixRadius ε))
      ∙ cong rat
          (·／ A (ε /4₊))

    scaledPrefixBound :
      partialSum
        (λ i →
          absℝ (a i)
            · rat (fst (prefixRadius ε)))
        (prefixLength ε)
        ≤ℝ
      rat (fst (ε /4₊))
    scaledPrefixBound =
      subst2 _≤ℝ_
        (sym
          (partialSum-right-scale
            (absℝ ∘ a)
            (rat (fst (prefixRadius ε)))
            (prefixLength ε)))
        rationalProductPath
        productBound

  globalDifferenceBound :
    ∀ n i →
    absℝ
      ( partialSum b n
      - partialSum b (n ∸ i)
      )
      ≤ℝ
    rat (fst doubleB)
  globalDifferenceBound n i =
    subst
      (absℝ
        ( partialSum b n
        - partialSum b (n ∸ i)
        )
        ≤ℝ_)
      (rat+rat (fst B) (fst B))
      (≤ℝ-trans
        (absℝ
          ( partialSum b n
          - partialSum b (n ∸ i)
          ))
        ( absℝ (partialSum b n)
        + absℝ (partialSum b (n ∸ i))
        )
        (rat (fst B) + rat (fst B))
        (absSubTriangle
          (partialSum b n)
          (partialSum b (n ∸ i)))
        (≤ℝ-add
          (absℝ (partialSum b n))
          (rat (fst B))
          (absℝ (partialSum b (n ∸ i)))
          (rat (fst B))
          (b-bounded n)
          (b-bounded (n ∸ i))))

  tailTermBound :
    ∀ ε n j →
    dropSeries
      (prefixLength ε)
      (cauchyProductRemainderMajorant a b n)
      j
      ≤ℝ
    absℝ (a (j +ℕ prefixLength ε))
      · rat (fst doubleB)
  tailTermBound ε n j =
    mulMonoL≤
      (absℝ
        ( partialSum b n
        - partialSum b
            (n ∸ (j +ℕ prefixLength ε))
        ))
      (rat (fst doubleB))
      (absℝ (a (j +ℕ prefixLength ε)))
      (absNonnegative
        (a (j +ℕ prefixLength ε)))
      (globalDifferenceBound
        n (j +ℕ prefixLength ε))

  prefixLength≤index :
    ∀ ε n →
    mertensModulus ε ℕ.≤ n →
    prefixLength ε ℕ.≤ n
  prefixLength≤index ε n modulus≤n =
    ℕ.≤-trans
      ℕ.≤SumRight
      modulus≤n

  absoluteTailAsDifference :
    ∀ ε n →
    (prefix≤n :
      prefixLength ε ℕ.≤ n) →
    partialSum
      (dropSeries
        (prefixLength ε)
        (absℝ ∘ a))
      (n ∸ prefixLength ε)
      ≡
    partialSum (absℝ ∘ a) n
      - partialSum (absℝ ∘ a)
          (prefixLength ε)
  absoluteTailAsDifference
    ε n prefix≤n =
      partialSum-drop
        (prefixLength ε)
        (absℝ ∘ a)
        (n ∸ prefixLength ε)
      ∙ cong
          (_-
            partialSum (absℝ ∘ a)
              (prefixLength ε))
          (cong
            (partialSum (absℝ ∘ a))
            (ℕ.[n-m]+m
              (prefixLength ε)
              n prefix≤n))

  absoluteTailBound :
    ∀ ε n →
    (modulus≤n :
      mertensModulus ε ℕ.≤ n) →
    partialSum
      (dropSeries
        (prefixLength ε)
        (absℝ ∘ a))
      (n ∸ prefixLength ε)
      <ℝ
    rat (fst (tailRadius ε))
  absoluteTailBound ε n modulus≤n =
    subst
      (_<ℝ rat (fst (tailRadius ε)))
      (sym
        (absoluteTailAsDifference
          ε n prefix≤n))
      (≤<ℝ-trans
        difference
        (absℝ difference)
        (rat (fst (tailRadius ε)))
        (leAbs difference)
        (closeness→absDifference<
          (partialSum (absℝ ∘ a) n)
          (partialSum (absℝ ∘ a)
            (prefixLength ε))
          (tailRadius ε)
          (snd a-absolute-cauchy
            (tailRadius ε)
            n (prefixLength ε)
            prefix≤n ℕ.≤-refl)))
    where
    prefix≤n :
      prefixLength ε ℕ.≤ n
    prefix≤n =
      prefixLength≤index ε n modulus≤n

    difference : ℝ
    difference =
      partialSum (absℝ ∘ a) n
        - partialSum (absℝ ∘ a)
            (prefixLength ε)

  tailMajorantBound :
    ∀ ε n →
    mertensModulus ε ℕ.≤ n →
    partialSum
      (dropSeries
        (prefixLength ε)
        (cauchyProductRemainderMajorant a b n))
      (n ∸ prefixLength ε)
      <ℝ
    rat (fst (ε /4₊))
  tailMajorantBound ε n modulus≤n =
    ≤<ℝ-trans
      (partialSum
        (dropSeries
          (prefixLength ε)
          (cauchyProductRemainderMajorant a b n))
        (n ∸ prefixLength ε))
      (partialSum
        scaledAbsoluteTail
        (n ∸ prefixLength ε))
      (rat (fst (ε /4₊)))
      (partialSumMono
        (dropSeries
          (prefixLength ε)
          (cauchyProductRemainderMajorant a b n))
        scaledAbsoluteTail
        (tailTermBound ε n)
        (n ∸ prefixLength ε))
      scaledAbsoluteTailBound
    where
    absoluteTail : RealSequence
    absoluteTail =
      dropSeries
        (prefixLength ε)
        (absℝ ∘ a)

    scaledAbsoluteTail : RealSequence
    scaledAbsoluteTail j =
      absoluteTail j
        · rat (fst doubleB)

    doubleBPositive :
      0 <ℝ rat (fst doubleB)
    doubleBPositive =
      <ℚ→<ℝ
        0 (fst doubleB)
        (snd doubleB)

    scaledProductBound :
      partialSum absoluteTail
          (n ∸ prefixLength ε)
        · rat (fst doubleB)
        <ℝ
      rat (fst (tailRadius ε))
        · rat (fst doubleB)
    scaledProductBound =
      mulMonoR<
        (partialSum absoluteTail
          (n ∸ prefixLength ε))
        (rat (fst (tailRadius ε)))
        (rat (fst doubleB))
        doubleBPositive
        (absoluteTailBound
          ε n modulus≤n)

    rationalProductPath :
      rat (fst (tailRadius ε))
        · rat (fst doubleB)
        ≡
      rat (fst (ε /4₊))
    rationalProductPath =
      mul-rat
        (fst (tailRadius ε))
        (fst doubleB)
      ∙ cong rat
          ( ℚ.·Comm
              (fst (tailRadius ε))
              (fst doubleB)
          ∙ ·／ doubleB (ε /4₊)
          )

    scaledAbsoluteTailBound :
      partialSum
        scaledAbsoluteTail
        (n ∸ prefixLength ε)
        <ℝ
      rat (fst (ε /4₊))
    scaledAbsoluteTailBound =
      subst2 _<ℝ_
        (sym
          (partialSum-right-scale
            absoluteTail
            (rat (fst doubleB))
            (n ∸ prefixLength ε)))
        rationalProductPath
        scaledProductBound

  fullMajorantBound :
    ∀ ε n →
    mertensModulus ε ℕ.≤ n →
    partialSum
      (cauchyProductRemainderMajorant a b n)
      n
      <ℝ
    rat (fst ε)
  fullMajorantBound ε n modulus≤n =
    <ℝ-trans
      (partialSum
        (cauchyProductRemainderMajorant a b n)
        n)
      (rat (fst (ε /2₊)))
      (rat (fst ε))
      majorantLessThanHalf
      (<ℚ→<ℝ
        (fst (ε /2₊))
        (fst ε)
        (/2₊<id ε))
    where
    prefix≤n :
      prefixLength ε ℕ.≤ n
    prefix≤n =
      prefixLength≤index ε n modulus≤n

    splitPath :
      partialSum
        (cauchyProductRemainderMajorant a b n)
        n
        ≡
      partialSum
        (cauchyProductRemainderMajorant a b n)
        (prefixLength ε)
      +
      partialSum
        (dropSeries
          (prefixLength ε)
          (cauchyProductRemainderMajorant a b n))
        (n ∸ prefixLength ε)
    splitPath =
      partialSum-splitAt
        (cauchyProductRemainderMajorant a b n)
        (prefixLength ε)
        n prefix≤n

    quarterSumPath :
      rat (fst (ε /4₊))
        + rat (fst (ε /4₊))
        ≡
      rat (fst (ε /2₊))
    quarterSumPath =
      rat+rat
        (fst (ε /4₊))
        (fst (ε /4₊))
      ∙ cong rat
          (1/2∈ℚ./4+/4≡/2
            (fst ε))

    splitBound :
      partialSum
        (cauchyProductRemainderMajorant a b n)
        (prefixLength ε)
      +
      partialSum
        (dropSeries
          (prefixLength ε)
          (cauchyProductRemainderMajorant a b n))
        (n ∸ prefixLength ε)
        <ℝ
      rat (fst (ε /4₊))
        + rat (fst (ε /4₊))
    splitBound =
      ≤<ℝ-add
        (partialSum
          (cauchyProductRemainderMajorant a b n)
          (prefixLength ε))
        (rat (fst (ε /4₊)))
        (partialSum
          (dropSeries
            (prefixLength ε)
            (cauchyProductRemainderMajorant a b n))
          (n ∸ prefixLength ε))
        (rat (fst (ε /4₊)))
        (prefixMajorantBound
          ε n modulus≤n)
        (tailMajorantBound
          ε n modulus≤n)

    majorantLessThanHalf :
      partialSum
        (cauchyProductRemainderMajorant a b n)
        n
        <ℝ
      rat (fst (ε /2₊))
    majorantLessThanHalf =
      subst2 _<ℝ_
        (sym splitPath)
        quarterSumPath
        splitBound

  selectedMertensRemainderModulus :
    CauchyProductRemainderModulus a b
  selectedMertensRemainderModulus .fst =
    mertensModulus
  selectedMertensRemainderModulus
    .snd ε n modulus≤n =
      ≤<ℝ-trans
        (absℝ
          (cauchyProductRemainder a b n))
        (partialSum
          (cauchyProductRemainderMajorant
            a b n)
          n)
        (rat (fst ε))
        (cauchyProductRemainderAbsBound
          a b n)
        (fullMajorantBound
          ε n modulus≤n)

mertensRectangularApproximation :
  ∀ A B a b →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  CauchyProductRectangularApproximation a b
mertensRectangularApproximation
  A B a b
  a-absolute-bounded b-bounded
  a-absolute-cauchy b-cauchy =
    remainderVanishes→rectangularApproximation
      a b
      (remainderModulus→remainderVanishes
        a b
        (selectedMertensRemainderModulus
          A B a b
          a-absolute-bounded b-bounded
          a-absolute-cauchy b-cauchy))

mertensCauchyProductIsCauchy :
  ∀ A B a b →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  IsCauchySeries (cauchyProduct a b)
mertensCauchyProductIsCauchy
  A B a b
  a-absolute-bounded b-bounded
  a-absolute-cauchy b-cauchy =
    cauchyProductIsCauchyWithRemainderModulus
      combinedBound a b
      a-combined-bounded
      b-combined-bounded
      (absoluteCauchySeriesIsCauchy
        a a-absolute-cauchy)
      b-cauchy
      (selectedMertensRemainderModulus
        A B a b
        a-absolute-bounded b-bounded
        a-absolute-cauchy b-cauchy)
  where
  combinedBound : ℚ₊
  combinedBound =
    A +₊ B

  ratA≤combined :
    rat (fst A) ≤ℝ
    rat (fst combinedBound)
  ratA≤combined =
    ≤ℚ→≤ℝ
      (fst A)
      (fst combinedBound)
      (ℚ.<Weaken≤
        (fst A)
        (fst combinedBound)
        (<₊SumLeft A B))

  ratB≤combined :
    rat (fst B) ≤ℝ
    rat (fst combinedBound)
  ratB≤combined =
    ≤ℚ→≤ℝ
      (fst B)
      (fst combinedBound)
      (ℚ.<Weaken≤
        (fst B)
        (fst combinedBound)
        (<₊SumRight B A))

  a-combined-bounded :
    UniformPartialSumAbsBound
      combinedBound a
  a-combined-bounded n =
    ≤ℝ-trans
      (absℝ (partialSum a n))
      (rat (fst A))
      (rat (fst combinedBound))
      (uniformAbsoluteBound→uniformBound
        A a a-absolute-bounded n)
      ratA≤combined

  b-combined-bounded :
    UniformPartialSumAbsBound
      combinedBound b
  b-combined-bounded n =
    ≤ℝ-trans
      (absℝ (partialSum b n))
      (rat (fst B))
      (rat (fst combinedBound))
      (b-bounded n)
      ratB≤combined

mertensCauchyProductSummable :
  ∀ A B a b →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  Summable (cauchyProduct a b)
mertensCauchyProductSummable
  A B a b
  a-absolute-bounded b-bounded
  a-absolute-cauchy b-cauchy =
    cauchyProductSummableWithRemainderModulus
      a b
      (absoluteCauchySeriesIsSummable
        a a-absolute-cauchy)
      (cauchySeriesIsSummable b b-cauchy)
      (selectedMertensRemainderModulus
        A B a b
        a-absolute-bounded b-bounded
        a-absolute-cauchy b-cauchy)

mertensSeriesSum-cauchyProduct :
  ∀ A B a b →
  (a-absolute-bounded :
    UniformAbsolutePartialSumBound A a) →
  (b-bounded :
    UniformPartialSumAbsBound B b) →
  (a-absolute-cauchy :
    IsAbsolutelyCauchySeries a) →
  (b-cauchy :
    IsCauchySeries b) →
  (product-summable :
    Summable (cauchyProduct a b)) →
  seriesSum (cauchyProduct a b)
      product-summable
    ≡
  seriesSum a
      (absoluteCauchySeriesIsSummable
        a a-absolute-cauchy)
    ·
  seriesSum b
      (cauchySeriesIsSummable b b-cauchy)
mertensSeriesSum-cauchyProduct
  A B a b
  a-absolute-bounded b-bounded
  a-absolute-cauchy b-cauchy
  product-summable =
    seriesSum-cauchyProduct
      a b
      (absoluteCauchySeriesIsSummable
        a a-absolute-cauchy)
      (cauchySeriesIsSummable b b-cauchy)
      product-summable
      (mertensRectangularApproximation
        A B a b
        a-absolute-bounded b-bounded
        a-absolute-cauchy b-cauchy)

mertensRectangularApproximationSym :
  ∀ A B a b →
  UniformPartialSumAbsBound A a →
  UniformAbsolutePartialSumBound B b →
  IsCauchySeries a →
  IsAbsolutelyCauchySeries b →
  CauchyProductRectangularApproximation a b
mertensRectangularApproximationSym
  A B a b
  a-bounded b-absolute-bounded
  a-cauchy b-absolute-cauchy ε =
    fst (swapped-approximation ε)
    , λ n modulus≤n →
        subst2 (_∼[ ε ]_)
          (mulComm
            (partialSum b n)
            (partialSum a n))
          (partialSum-pointwise
            (cauchyProduct b a)
            (cauchyProduct a b)
            (cauchyProduct-comm b a)
            n)
          (snd (swapped-approximation ε)
            n modulus≤n)
  where
  swapped-approximation :
    CauchyProductRectangularApproximation b a
  swapped-approximation =
    mertensRectangularApproximation
      B A b a
      b-absolute-bounded a-bounded
      b-absolute-cauchy a-cauchy

mertensCauchyProductIsCauchySym :
  ∀ A B a b →
  UniformPartialSumAbsBound A a →
  UniformAbsolutePartialSumBound B b →
  IsCauchySeries a →
  IsAbsolutelyCauchySeries b →
  IsCauchySeries (cauchyProduct a b)
mertensCauchyProductIsCauchySym
  A B a b
  a-bounded b-absolute-bounded
  a-cauchy b-absolute-cauchy =
    subst IsCauchySeries
      (cauchyProduct-comm-sequence b a)
      (mertensCauchyProductIsCauchy
        B A b a
        b-absolute-bounded a-bounded
        b-absolute-cauchy a-cauchy)

mertensCauchyProductSummableSym :
  ∀ A B a b →
  UniformPartialSumAbsBound A a →
  UniformAbsolutePartialSumBound B b →
  IsCauchySeries a →
  IsAbsolutelyCauchySeries b →
  Summable (cauchyProduct a b)
mertensCauchyProductSummableSym
  A B a b
  a-bounded b-absolute-bounded
  a-cauchy b-absolute-cauchy =
    subst Summable
      (cauchyProduct-comm-sequence b a)
      (mertensCauchyProductSummable
        B A b a
        b-absolute-bounded a-bounded
        b-absolute-cauchy a-cauchy)

mertensSeriesSum-cauchyProductSym :
  ∀ A B a b →
  (a-bounded :
    UniformPartialSumAbsBound A a) →
  (b-absolute-bounded :
    UniformAbsolutePartialSumBound B b) →
  (a-cauchy :
    IsCauchySeries a) →
  (b-absolute-cauchy :
    IsAbsolutelyCauchySeries b) →
  (product-summable :
    Summable (cauchyProduct a b)) →
  seriesSum (cauchyProduct a b)
      product-summable
    ≡
  seriesSum a
      (cauchySeriesIsSummable
        a a-cauchy)
    ·
  seriesSum b
      (absoluteCauchySeriesIsSummable
        b b-absolute-cauchy)
mertensSeriesSum-cauchyProductSym
  A B a b
  a-bounded b-absolute-bounded
  a-cauchy b-absolute-cauchy
  product-summable =
    seriesSum-cauchyProduct
      a b
      (cauchySeriesIsSummable
        a a-cauchy)
      (absoluteCauchySeriesIsSummable
        b b-absolute-cauchy)
      product-summable
      (mertensRectangularApproximationSym
        A B a b
        a-bounded b-absolute-bounded
        a-cauchy b-absolute-cauchy)

absoluteMertensCauchyProductIsCauchy :
  ∀ A B a b →
  (a-absolute :
    IsAbsolutelyCauchySeries a) →
  (b-absolute :
    IsAbsolutelyCauchySeries b) →
  AbsoluteCauchySeriesSumBound
    A a a-absolute →
  AbsoluteCauchySeriesSumBound
    B b b-absolute →
  IsCauchySeries (cauchyProduct a b)
absoluteMertensCauchyProductIsCauchy
  A B a b
  a-absolute b-absolute
  a-sum-bounded b-sum-bounded =
    mertensCauchyProductIsCauchy
      A B a b
      (absoluteCauchySumBound→uniformAbsoluteBound
        A a a-absolute a-sum-bounded)
      (uniformAbsoluteBound→uniformBound
        B b
        (absoluteCauchySumBound→uniformAbsoluteBound
          B b b-absolute b-sum-bounded))
      a-absolute
      (absoluteCauchySeriesIsCauchy
        b b-absolute)

absoluteMertensCauchyProductSummable :
  ∀ A B a b →
  (a-absolute :
    IsAbsolutelyCauchySeries a) →
  (b-absolute :
    IsAbsolutelyCauchySeries b) →
  AbsoluteCauchySeriesSumBound
    A a a-absolute →
  AbsoluteCauchySeriesSumBound
    B b b-absolute →
  Summable (cauchyProduct a b)
absoluteMertensCauchyProductSummable
  A B a b
  a-absolute b-absolute
  a-sum-bounded b-sum-bounded =
    mertensCauchyProductSummable
      A B a b
      (absoluteCauchySumBound→uniformAbsoluteBound
        A a a-absolute a-sum-bounded)
      (uniformAbsoluteBound→uniformBound
        B b
        (absoluteCauchySumBound→uniformAbsoluteBound
          B b b-absolute b-sum-bounded))
      a-absolute
      (absoluteCauchySeriesIsCauchy
        b b-absolute)

absoluteMertensSeriesSum-cauchyProduct :
  ∀ A B a b →
  (a-absolute :
    IsAbsolutelyCauchySeries a) →
  (b-absolute :
    IsAbsolutelyCauchySeries b) →
  (a-sum-bounded :
    AbsoluteCauchySeriesSumBound
      A a a-absolute) →
  (b-sum-bounded :
    AbsoluteCauchySeriesSumBound
      B b b-absolute) →
  (product-summable :
    Summable (cauchyProduct a b)) →
  seriesSum (cauchyProduct a b)
      product-summable
    ≡
  seriesSum a
      (absoluteCauchySeriesIsSummable
        a a-absolute)
    ·
  seriesSum b
      (absoluteCauchySeriesIsSummable
        b b-absolute)
absoluteMertensSeriesSum-cauchyProduct
  A B a b
  a-absolute b-absolute
  a-sum-bounded b-sum-bounded
  product-summable =
    mertensSeriesSum-cauchyProduct
      A B a b
      (absoluteCauchySumBound→uniformAbsoluteBound
        A a a-absolute a-sum-bounded)
      (uniformAbsoluteBound→uniformBound
        B b
        (absoluteCauchySumBound→uniformAbsoluteBound
          B b b-absolute b-sum-bounded))
      a-absolute
      (absoluteCauchySeriesIsCauchy
        b b-absolute)
      product-summable

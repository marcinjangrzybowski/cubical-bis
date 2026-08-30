module Cubical.Analysis.Real.Series.Product.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc; _∸_)
  renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Bounds
open import Cubical.Analysis.Real.Series.Tails
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Product.Finite


open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ


private
  ≤ℚ→≤ℝ : ∀ p q → p ℚ.≤ q → rat p ≤ℝ rat q
  ≤ℚ→≤ℝ p q = invEq (rat≤rat≃ p q)


UniformAbsolutePartialSumBound :
  ℚ₊ → RealSequence → Type₀
UniformAbsolutePartialSumBound bound terms =
  ∀ n →
  partialSum (absℝ ∘ terms) n ≤ℝ rat (fst bound)


UniformPartialSumAbsBound :
  ℚ₊ → RealSequence → Type₀
UniformPartialSumAbsBound bound terms =
  ∀ n → absℝ (partialSum terms n) ≤ℝ rat (fst bound)


uniformAbsoluteBound→uniformBound : ∀ bound terms →
  UniformAbsolutePartialSumBound bound terms →
  UniformPartialSumAbsBound bound terms
uniformAbsoluteBound→uniformBound bound terms absoluteBound n =
  ≤ℝ-trans
    (absℝ (partialSum terms n))
    (partialSum (absℝ ∘ terms) n)
    (rat (fst bound))
    (partialSumAbsBound terms n)
    (absoluteBound n)


absolutePartialSumLeSeriesSum : ∀ terms →
  (absoluteSummable : AbsolutelySummable terms) →
  ∀ n →
  partialSum (absℝ ∘ terms) n ≤ℝ
  seriesSum (absℝ ∘ terms) absoluteSummable
absolutePartialSumLeSeriesSum terms absoluteSummable n =
  eventuallyLePresLimits
    (∣ (n
      , λ k n≤k →
          partialSumIndexMono
            (absℝ ∘ terms)
            (λ i → absNonnegative (terms i))
            n k n≤k)
      ∣₁)
    (constantIsLimitSequence
      (partialSum (absℝ ∘ terms) n))
    (seriesSumHasSum
      (absℝ ∘ terms) absoluteSummable)


absoluteSeriesSumBound→uniformAbsoluteBound : ∀ bound terms →
  (absoluteSummable : AbsolutelySummable terms) →
  seriesSum (absℝ ∘ terms) absoluteSummable
    ≤ℝ rat (fst bound) →
  UniformAbsolutePartialSumBound bound terms
absoluteSeriesSumBound→uniformAbsoluteBound
    bound terms absoluteSummable sumBound n =
  ≤ℝ-trans
    (partialSum (absℝ ∘ terms) n)
    (seriesSum (absℝ ∘ terms) absoluteSummable)
    (rat (fst bound))
    (absolutePartialSumLeSeriesSum
      terms absoluteSummable n)
    sumBound


AbsoluteCauchySeriesSumBound :
  ℚ₊ → (terms : RealSequence) →
  IsAbsolutelyCauchySeries terms → Type₀
AbsoluteCauchySeriesSumBound bound terms absolute =
  seriesSum (absℝ ∘ terms)
      (absoluteCauchySeriesIsAbsolutelySummable terms absolute)
    ≤ℝ
  rat (fst bound)


absoluteCauchySumBound→uniformAbsoluteBound : ∀ bound terms absolute →
  AbsoluteCauchySeriesSumBound bound terms absolute →
  UniformAbsolutePartialSumBound bound terms
absoluteCauchySumBound→uniformAbsoluteBound
    bound terms absolute =
  absoluteSeriesSumBound→uniformAbsoluteBound
    bound terms
    (absoluteCauchySeriesIsAbsolutelySummable terms absolute)


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
        (ℕ.≤-k+ (ℕ.<-weaken i<split))
        combined≤n))


partialSum-splitAt : ∀ terms split n →
  split ℕ.≤ n →
  partialSum terms n ≡
  partialSum terms split
    + partialSum (dropSeries split terms) (n ∸ split)
partialSum-splitAt terms split n split≤n =
  subst
    (λ k →
      partialSum terms k ≡
      partialSum terms split
        + partialSum (dropSeries split terms) (n ∸ split))
    (ℕ.[n-m]+m split n split≤n)
    (partialSum-drop-recombine split terms (n ∸ split))


partialSumMonoBefore : ∀ a b n →
  (∀ k → k ℕ.< n → a k ≤ℝ b k) →
  partialSum a n ≤ℝ partialSum b n
partialSumMonoBefore a b zero before =
  ≤ℝ-refl 0ℝ
partialSumMonoBefore a b (suc n) before =
  addPres≤
    (partialSum a n) (partialSum b n)
    (a n) (b n)
    (partialSumMonoBefore a b n
      (λ k k<n → before k (ℕ.<-trans k<n ℕ.<-suc)))
    (before n ℕ.<-suc)


module _
  (A B : ℚ₊)
  (a b : RealSequence)
  (aAbsoluteBounded : UniformAbsolutePartialSumBound A a)
  (bBounded : UniformPartialSumAbsBound B b)
  (aAbsoluteChosen :
    ChosenIsCauchySequence (partialSum (absℝ ∘ a)))
  (bChosen : ChosenIsCauchySequence (partialSum b))
  where

  doubleB : ℚ₊
  doubleB = B +₊ B

  prefixRadius : ℚ₊ → ℚ₊
  prefixRadius ε = (ε /4₊) ₊／₊ A

  tailRadius : ℚ₊ → ℚ₊
  tailRadius ε = (ε /4₊) ₊／₊ doubleB

  prefixLength : ℚ₊ → ℕ
  prefixLength ε =
    fst aAbsoluteChosen (tailRadius ε)

  separationLength : ℚ₊ → ℕ
  separationLength ε =
    fst bChosen (prefixRadius ε)

  mertensModulus : ℚ₊ → ℕ
  mertensModulus ε =
    separationLength ε +ℕ prefixLength ε

  prefixDifferenceBound :
    ∀ ε n i →
    i ℕ.< prefixLength ε →
    mertensModulus ε ℕ.≤ n →
    absℝ
      (partialSum b n - partialSum b (n ∸ i))
      ≤ℝ
    rat (fst (prefixRadius ε))
  prefixDifferenceBound
      ε n i i<prefix modulus≤n =
    <ℝ-weaken
      (absℝ
        (partialSum b n - partialSum b (n ∸ i)))
      (rat (fst (prefixRadius ε)))
      (closeness→absDifference<
        (partialSum b n)
        (partialSum b (n ∸ i))
        (prefixRadius ε)
        (snd bChosen
          (prefixRadius ε)
          n (n ∸ i)
          separation≤n separation≤remaining))
    where
    separation≤n : separationLength ε ℕ.≤ n
    separation≤n =
      ℕ.≤-trans ℕ.≤SumLeft modulus≤n

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
    cauchyProductRemainderMajorant a b n i ≤ℝ
    absℝ (a i) · rat (fst (prefixRadius ε))
  prefixTermBound
      ε n i i<prefix modulus≤n =
    mulPres≤L
      (absℝ
        (partialSum b n - partialSum b (n ∸ i)))
      (rat (fst (prefixRadius ε)))
      (absℝ (a i))
      (0≤→isNonnegative
        (absℝ (a i)) (absNonnegative (a i)))
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
        (λ i → absℝ (a i) · rat (fst (prefixRadius ε)))
        (prefixLength ε))
      (rat (fst (ε /4₊)))
      (partialSumMonoBefore
        (cauchyProductRemainderMajorant a b n)
        (λ i → absℝ (a i) · rat (fst (prefixRadius ε)))
        (prefixLength ε)
        (λ i i<prefix →
          prefixTermBound ε n i i<prefix modulus≤n))
      scaledPrefixBound
    where
    radiusNonnegative :
      0ℝ ≤ℝ rat (fst (prefixRadius ε))
    radiusNonnegative =
      ≤ℚ→≤ℝ 0 (fst (prefixRadius ε))
        (ℚ.<Weaken≤ 0 (fst (prefixRadius ε))
          (snd (prefixRadius ε)))

    productBound :
      partialSum (absℝ ∘ a) (prefixLength ε)
          · rat (fst (prefixRadius ε))
        ≤ℝ
      rat (fst A) · rat (fst (prefixRadius ε))
    productBound =
      mulPres≤R
        (partialSum (absℝ ∘ a) (prefixLength ε))
        (rat (fst A))
        (rat (fst (prefixRadius ε)))
        (0≤→isNonnegative
          (rat (fst (prefixRadius ε))) radiusNonnegative)
        (aAbsoluteBounded (prefixLength ε))

    rationalProductPath :
      rat (fst A) · rat (fst (prefixRadius ε)) ≡
      rat (fst (ε /4₊))
    rationalProductPath =
      mul-rat (fst A) (fst (prefixRadius ε))
      ∙ cong rat (·／ A (ε /4₊))

    scaledPrefixBound :
      partialSum
        (λ i → absℝ (a i) · rat (fst (prefixRadius ε)))
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

  globalDifferenceBound : ∀ n i →
    absℝ (partialSum b n - partialSum b (n ∸ i)) ≤ℝ
    rat (fst doubleB)
  globalDifferenceBound n i =
    subst
      (absℝ (partialSum b n - partialSum b (n ∸ i)) ≤ℝ_)
      (rat+rat (fst B) (fst B))
      (≤ℝ-trans
        (absℝ (partialSum b n - partialSum b (n ∸ i)))
        (absℝ (partialSum b n)
          + absℝ (partialSum b (n ∸ i)))
        (rat (fst B) + rat (fst B))
        (absSubTriangle
          (partialSum b n) (partialSum b (n ∸ i)))
        (addPres≤
          (absℝ (partialSum b n)) (rat (fst B))
          (absℝ (partialSum b (n ∸ i))) (rat (fst B))
          (bBounded n) (bBounded (n ∸ i))))

  tailTermBound : ∀ ε n j →
    dropSeries
      (prefixLength ε)
      (cauchyProductRemainderMajorant a b n)
      j
      ≤ℝ
    absℝ (a (j +ℕ prefixLength ε))
      · rat (fst doubleB)
  tailTermBound ε n j =
    mulPres≤L
      (absℝ
        (partialSum b n
          - partialSum b (n ∸ (j +ℕ prefixLength ε))))
      (rat (fst doubleB))
      (absℝ (a (j +ℕ prefixLength ε)))
      (0≤→isNonnegative
        (absℝ (a (j +ℕ prefixLength ε)))
        (absNonnegative (a (j +ℕ prefixLength ε))))
      (globalDifferenceBound n (j +ℕ prefixLength ε))

  prefixLength≤index : ∀ ε n →
    mertensModulus ε ℕ.≤ n →
    prefixLength ε ℕ.≤ n
  prefixLength≤index ε n modulus≤n =
    ℕ.≤-trans ℕ.≤SumRight modulus≤n

  absoluteTailAsDifference : ∀ ε n →
    (prefix≤n : prefixLength ε ℕ.≤ n) →
    partialSum
      (dropSeries (prefixLength ε) (absℝ ∘ a))
      (n ∸ prefixLength ε)
      ≡
    partialSum (absℝ ∘ a) n
      - partialSum (absℝ ∘ a) (prefixLength ε)
  absoluteTailAsDifference ε n prefix≤n =
    partialSum-drop
      (prefixLength ε) (absℝ ∘ a)
      (n ∸ prefixLength ε)
    ∙ cong
        (_- partialSum (absℝ ∘ a) (prefixLength ε))
        (cong (partialSum (absℝ ∘ a))
          (ℕ.[n-m]+m (prefixLength ε) n prefix≤n))

  absoluteTailBound : ∀ ε n →
    (modulus≤n : mertensModulus ε ℕ.≤ n) →
    partialSum
      (dropSeries (prefixLength ε) (absℝ ∘ a))
      (n ∸ prefixLength ε)
      <ℝ
    rat (fst (tailRadius ε))
  absoluteTailBound ε n modulus≤n =
    subst
      (_<ℝ rat (fst (tailRadius ε)))
      (sym (absoluteTailAsDifference ε n prefix≤n))
      (≤<ℝ-trans
        difference (absℝ difference)
        (rat (fst (tailRadius ε)))
        (leAbs difference)
        (closeness→absDifference<
          (partialSum (absℝ ∘ a) n)
          (partialSum (absℝ ∘ a) (prefixLength ε))
          (tailRadius ε)
          (snd aAbsoluteChosen
            (tailRadius ε)
            n (prefixLength ε)
            prefix≤n ℕ.≤-refl)))
    where
    prefix≤n : prefixLength ε ℕ.≤ n
    prefix≤n = prefixLength≤index ε n modulus≤n

    difference : ℝ
    difference =
      partialSum (absℝ ∘ a) n
        - partialSum (absℝ ∘ a) (prefixLength ε)

  tailMajorantBound : ∀ ε n →
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
      (partialSum scaledAbsoluteTail (n ∸ prefixLength ε))
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
    absoluteTail = dropSeries (prefixLength ε) (absℝ ∘ a)

    scaledAbsoluteTail : RealSequence
    scaledAbsoluteTail j =
      absoluteTail j · rat (fst doubleB)

    doubleBPositive : 0ℝ <ℝ rat (fst doubleB)
    doubleBPositive =
      <ℚ→<ℝ 0 (fst doubleB) (snd doubleB)

    scaledProductBound :
      partialSum absoluteTail (n ∸ prefixLength ε)
          · rat (fst doubleB)
        <ℝ
      rat (fst (tailRadius ε)) · rat (fst doubleB)
    scaledProductBound =
      mulPres<PosR
        (partialSum absoluteTail (n ∸ prefixLength ε))
        (rat (fst (tailRadius ε)))
        (rat (fst doubleB))
        doubleBPositive
        (absoluteTailBound ε n modulus≤n)

    rationalProductPath :
      rat (fst (tailRadius ε)) · rat (fst doubleB) ≡
      rat (fst (ε /4₊))
    rationalProductPath =
      mul-rat (fst (tailRadius ε)) (fst doubleB)
      ∙ cong rat
          (ℚ.·Comm (fst (tailRadius ε)) (fst doubleB)
          ∙ ·／ doubleB (ε /4₊))

    scaledAbsoluteTailBound :
      partialSum scaledAbsoluteTail (n ∸ prefixLength ε)
        <ℝ
      rat (fst (ε /4₊))
    scaledAbsoluteTailBound =
      subst2 _<ℝ_
        (sym
          (partialSum-right-scale
            absoluteTail (rat (fst doubleB))
            (n ∸ prefixLength ε)))
        rationalProductPath
        scaledProductBound

  fullMajorantBound : ∀ ε n →
    mertensModulus ε ℕ.≤ n →
    partialSum (cauchyProductRemainderMajorant a b n) n
      <ℝ
    rat (fst ε)
  fullMajorantBound ε n modulus≤n =
    <ℝ-trans
      (partialSum (cauchyProductRemainderMajorant a b n) n)
      (rat (fst (ε /2₊)))
      (rat (fst ε))
      majorantLessThanHalf
      (<ℚ→<ℝ
        (fst (ε /2₊)) (fst ε) (/2₊<id ε))
    where
    prefix≤n : prefixLength ε ℕ.≤ n
    prefix≤n = prefixLength≤index ε n modulus≤n

    splitPath :
      partialSum (cauchyProductRemainderMajorant a b n) n ≡
      partialSum
        (cauchyProductRemainderMajorant a b n)
        (prefixLength ε)
      + partialSum
          (dropSeries
            (prefixLength ε)
            (cauchyProductRemainderMajorant a b n))
          (n ∸ prefixLength ε)
    splitPath =
      partialSum-splitAt
        (cauchyProductRemainderMajorant a b n)
        (prefixLength ε) n prefix≤n

    quarterSumPath :
      rat (fst (ε /4₊)) + rat (fst (ε /4₊)) ≡
      rat (fst (ε /2₊))
    quarterSumPath =
      rat+rat (fst (ε /4₊)) (fst (ε /4₊))
      ∙ cong rat (/4+/4≡/2 (fst ε))

    splitBound :
      partialSum
        (cauchyProductRemainderMajorant a b n)
        (prefixLength ε)
      + partialSum
          (dropSeries
            (prefixLength ε)
            (cauchyProductRemainderMajorant a b n))
          (n ∸ prefixLength ε)
        <ℝ
      rat (fst (ε /4₊)) + rat (fst (ε /4₊))
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
        (prefixMajorantBound ε n modulus≤n)
        (tailMajorantBound ε n modulus≤n)

    majorantLessThanHalf :
      partialSum (cauchyProductRemainderMajorant a b n) n
        <ℝ
      rat (fst (ε /2₊))
    majorantLessThanHalf =
      subst2 _<ℝ_
        (sym splitPath) quarterSumPath splitBound

  chosenMertensRemainderLimit :
    isLimitSequence (cauchyProductRemainder a b) 0ℝ
  chosenMertensRemainderLimit ε =
    ∣ (mertensModulus ε
    , λ n modulus≤n →
        absDifference<→closeness
          (cauchyProductRemainder a b n) 0ℝ ε
          (subst
            (_<ℝ rat (fst ε))
            (sym
              (cong absℝ
                (subZero (cauchyProductRemainder a b n))))
            (≤<ℝ-trans
              (absℝ (cauchyProductRemainder a b n))
              (partialSum
                (cauchyProductRemainderMajorant a b n) n)
              (rat (fst ε))
              (cauchyProductRemainderAbsBound a b n)
              (fullMajorantBound ε n modulus≤n)))
    )
    ∣₁


mertensRemainderLimit : ∀ A B a b →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  isLimitSequence (cauchyProductRemainder a b) 0ℝ
mertensRemainderLimit
    A B a b aAbsoluteBounded bBounded
    aAbsoluteCauchy bCauchy =
  PT.rec
    (isPropIsLimitSequence (cauchyProductRemainder a b) 0ℝ)
    withAbsoluteChosen
    aAbsoluteCauchy
  where
  withAbsoluteChosen :
    ChosenIsCauchySequence (partialSum (absℝ ∘ a)) →
    isLimitSequence (cauchyProductRemainder a b) 0ℝ
  withAbsoluteChosen aAbsoluteChosen =
    PT.rec
      (isPropIsLimitSequence (cauchyProductRemainder a b) 0ℝ)
      (λ bChosen →
        chosenMertensRemainderLimit
          A B a b aAbsoluteBounded bBounded
          aAbsoluteChosen bChosen)
      bCauchy


mertensCauchyProductHasSum : ∀ A B a b aSum bSum →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  HasSum a aSum →
  HasSum b bSum →
  HasSum (cauchyProduct a b) (aSum · bSum)
mertensCauchyProductHasSum
    A B a b aSum bSum
    aAbsoluteBounded bBounded
    aAbsoluteCauchy bCauchy aHasSum bHasSum =
  cauchyProductHasSumWithRemainderLimit
    a b aSum bSum aHasSum bHasSum
    (mertensRemainderLimit
      A B a b aAbsoluteBounded bBounded
      aAbsoluteCauchy bCauchy)


mertensCauchyProductSummable : ∀ A B a b →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  Summable (cauchyProduct a b)
mertensCauchyProductSummable
    A B a b aAbsoluteBounded bBounded
    aAbsoluteCauchy bCauchy =
  cauchyProductSummableWithRemainderLimit
    a b
    (absoluteCauchySeriesIsSummable a aAbsoluteCauchy)
    (cauchySeriesIsSummable b bCauchy)
    (mertensRemainderLimit
      A B a b aAbsoluteBounded bBounded
      aAbsoluteCauchy bCauchy)


mertensSeriesSum-cauchyProduct : ∀ A B a b →
  (aAbsoluteBounded : UniformAbsolutePartialSumBound A a) →
  (bBounded : UniformPartialSumAbsBound B b) →
  (aAbsoluteCauchy : IsAbsolutelyCauchySeries a) →
  (bCauchy : IsCauchySeries b) →
  (productSummable : Summable (cauchyProduct a b)) →
  seriesSum (cauchyProduct a b) productSummable ≡
  seriesSum a (absoluteCauchySeriesIsSummable a aAbsoluteCauchy)
    · seriesSum b (cauchySeriesIsSummable b bCauchy)
mertensSeriesSum-cauchyProduct
    A B a b aAbsoluteBounded bBounded
    aAbsoluteCauchy bCauchy productSummable =
  seriesSum-cauchyProductWithRemainderLimit
    a b
    (absoluteCauchySeriesIsSummable a aAbsoluteCauchy)
    (cauchySeriesIsSummable b bCauchy)
    productSummable
    (mertensRemainderLimit
      A B a b aAbsoluteBounded bBounded
      aAbsoluteCauchy bCauchy)

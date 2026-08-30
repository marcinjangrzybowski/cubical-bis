module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.ConvolutionMertens where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ ; _∸_)
  renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Inverse

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

private
  module ℚ where
    open import Cubical.Data.Rationals.Base public
    open import Cubical.Data.Rationals.Properties public
    open import Cubical.Data.Rationals.Order public
    open import Cubical.Data.Rationals.Order.Algebra public

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs ; add-monotone ; abs-triangle)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Multiplication
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (closeness→absDifference< ; absDifference<→closeness)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Order
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.FiniteSum
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Bounds
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Convolution


remainingIndexAbove : ∀ minimum split n i →
  i ℕ.< split → minimum +ℕ split ℕ.≤ n →
  minimum ℕ.≤ n ∸ i
remainingIndexAbove minimum split n i i<split combined≤n =
  subst (λ k → k ℕ.≤ n ∸ i)
    (ℕ.+∸ minimum i)
    (ℕ.≤-∸-≤
      (minimum +ℕ i) n i
      (ℕ.≤-trans
        (ℕ.≤-k+ (ℕ.<-weaken i<split))
        combined≤n))


partialSum-splitAt : ∀ terms split n →
  split ℕ.≤ n →
  partialSum terms n ≡
  partialSum terms split Add.+
    partialSum (dropSeries split terms) (n ∸ split)
partialSum-splitAt terms split n split≤n =
  subst
    (λ k →
      partialSum terms k ≡
      partialSum terms split Add.+
        partialSum (dropSeries split terms) (n ∸ split))
    (ℕ.[n-m]+m split n split≤n)
    (partialSum-drop-recombine split terms (n ∸ split))


private
  abs-sub-triangle : ∀ x y →
    Abs.absℝ (x Group.- y) ≤ℝ
    Abs.absℝ x Add.+ Abs.absℝ y
  abs-sub-triangle x y =
    subst (λ z → Abs.absℝ (x Group.- y) ≤ℝ Abs.absℝ x Add.+ z)
      (Abs.absℝ-neg y)
      (abs-triangle x (Neg.- y))


module _
  (A B : ℚ₊)
  (a b : RealSequence)
  (a-absolute-bounded : UniformAbsolutePartialSumBound A a)
  (b-bounded : UniformPartialSumAbsBound B b)
  where

  doubleB : ℚ₊
  doubleB = B +₊ B

  prefixRadius : ℚ₊ → ℚ₊
  prefixRadius ε = (ε /4₊) ₊／₊ A

  tailRadius : ℚ₊ → ℚ₊
  tailRadius ε = (ε /4₊) ₊／₊ doubleB

  module _
    (ε : ℚ₊)
    (a-tail : CauchyTail
      (partialSum (Abs.absℝ ∘ a)) (tailRadius ε))
    (b-tail : CauchyTail (partialSum b) (prefixRadius ε))
    where

    prefixLength : ℕ
    prefixLength = fst a-tail

    separationLength : ℕ
    separationLength = fst b-tail

    mertensIndex : ℕ
    mertensIndex = separationLength +ℕ prefixLength

    prefixDifferenceBound : ∀ n i →
      i ℕ.< prefixLength → mertensIndex ℕ.≤ n →
      Abs.absℝ
        (partialSum b n Group.- partialSum b (n ∸ i)) ≤ℝ
      Real.ιℚ (fst (prefixRadius ε))
    prefixDifferenceBound n i i<prefix index≤n =
      <ℝ-weaken
        (Abs.absℝ
          (partialSum b n Group.- partialSum b (n ∸ i)))
        (Real.ιℚ (fst (prefixRadius ε)))
        (closeness→absDifference<
          (partialSum b n) (partialSum b (n ∸ i))
          (prefixRadius ε)
          (snd b-tail n (n ∸ i)
            separation≤n separation≤remaining))
      where
      separation≤n : separationLength ℕ.≤ n
      separation≤n =
        ℕ.≤-trans ℕ.≤SumLeft index≤n

      separation≤remaining : separationLength ℕ.≤ n ∸ i
      separation≤remaining =
        remainingIndexAbove separationLength prefixLength
          n i i<prefix index≤n

    prefixTermBound : ∀ n i →
      i ℕ.< prefixLength → mertensIndex ℕ.≤ n →
      cauchyProductRemainderMajorant a b n i ≤ℝ
      Abs.absℝ (a i) Mul.·
        Real.ιℚ (fst (prefixRadius ε))
    prefixTermBound n i i<prefix index≤n =
      mul-preserves≤-left-nonnegative
        (Abs.absℝ
          (partialSum b n Group.- partialSum b (n ∸ i)))
        (Real.ιℚ (fst (prefixRadius ε)))
        (Abs.absℝ (a i))
        (prefixDifferenceBound n i i<prefix index≤n)
        (zero≤abs (a i))

    prefixMajorantBound : ∀ n →
      mertensIndex ℕ.≤ n →
      partialSum (cauchyProductRemainderMajorant a b n)
        prefixLength ≤ℝ
      Real.ιℚ (fst (ε /4₊))
    prefixMajorantBound n index≤n =
      ≤ℝ-trans
        (partialSum (cauchyProductRemainderMajorant a b n)
          prefixLength)
        (partialSum
          (λ i → Abs.absℝ (a i) Mul.·
            Real.ιℚ (fst (prefixRadius ε)))
          prefixLength)
        (Real.ιℚ (fst (ε /4₊)))
        (partialSumMonoBefore
          (cauchyProductRemainderMajorant a b n)
          (λ i → Abs.absℝ (a i) Mul.·
            Real.ιℚ (fst (prefixRadius ε)))
          prefixLength
          (λ i i<prefix →
            prefixTermBound n i i<prefix index≤n))
        scaledPrefixBound
      where
      radiusNonnegative :
        zeroℝ ≤ℝ Real.ιℚ (fst (prefixRadius ε))
      radiusNonnegative =
        ≤ℚ→≤ℝ 0 (fst (prefixRadius ε))
          (ℚ.<Weaken≤ 0 (fst (prefixRadius ε))
            (snd (prefixRadius ε)))

      productBound :
        partialSum (Abs.absℝ ∘ a) prefixLength Mul.·
            Real.ιℚ (fst (prefixRadius ε)) ≤ℝ
        Real.ιℚ (fst A) Mul.·
            Real.ιℚ (fst (prefixRadius ε))
      productBound =
        mul-preserves≤-right-nonnegative
          (partialSum (Abs.absℝ ∘ a) prefixLength)
          (Real.ιℚ (fst A))
          (Real.ιℚ (fst (prefixRadius ε)))
          (a-absolute-bounded prefixLength)
          radiusNonnegative

      rationalProductPath :
        Real.ιℚ (fst A) Mul.·
          Real.ιℚ (fst (prefixRadius ε)) ≡
        Real.ιℚ (fst (ε /4₊))
      rationalProductPath =
        Mul.mul-ι-ι (fst A) (fst (prefixRadius ε))
        ∙ cong Real.ιℚ (·／ A (ε /4₊))

      scaledPrefixBound :
        partialSum
          (λ i → Abs.absℝ (a i) Mul.·
            Real.ιℚ (fst (prefixRadius ε)))
          prefixLength ≤ℝ
        Real.ιℚ (fst (ε /4₊))
      scaledPrefixBound =
        subst2 _≤ℝ_
          (sym
            (partialSum-right-scale
              (Abs.absℝ ∘ a)
              (Real.ιℚ (fst (prefixRadius ε)))
              prefixLength))
          rationalProductPath productBound

    globalDifferenceBound : ∀ n i →
      Abs.absℝ
        (partialSum b n Group.- partialSum b (n ∸ i)) ≤ℝ
      Real.ιℚ (fst doubleB)
    globalDifferenceBound n i =
      subst
        (Abs.absℝ
          (partialSum b n Group.- partialSum b (n ∸ i)) ≤ℝ_)
        (Add.add-ι-ι (fst B) (fst B))
        (≤ℝ-trans
          (Abs.absℝ
            (partialSum b n Group.- partialSum b (n ∸ i)))
          (Abs.absℝ (partialSum b n) Add.+
            Abs.absℝ (partialSum b (n ∸ i)))
          (Real.ιℚ (fst B) Add.+ Real.ιℚ (fst B))
          (abs-sub-triangle
            (partialSum b n) (partialSum b (n ∸ i)))
          (add-monotone
            (Abs.absℝ (partialSum b n)) (Real.ιℚ (fst B))
            (Abs.absℝ (partialSum b (n ∸ i)))
              (Real.ιℚ (fst B))
            (b-bounded n) (b-bounded (n ∸ i))))

    tailTermBound : ∀ n j →
      dropSeries prefixLength
        (cauchyProductRemainderMajorant a b n) j ≤ℝ
      Abs.absℝ (a (j +ℕ prefixLength)) Mul.·
        Real.ιℚ (fst doubleB)
    tailTermBound n j =
      mul-preserves≤-left-nonnegative
        (Abs.absℝ
          (partialSum b n Group.-
            partialSum b (n ∸ (j +ℕ prefixLength))))
        (Real.ιℚ (fst doubleB))
        (Abs.absℝ (a (j +ℕ prefixLength)))
        (globalDifferenceBound n (j +ℕ prefixLength))
        (zero≤abs (a (j +ℕ prefixLength)))

    prefixLength≤index : ∀ n →
      mertensIndex ℕ.≤ n → prefixLength ℕ.≤ n
    prefixLength≤index n index≤n =
      ℕ.≤-trans ℕ.≤SumRight index≤n

    absoluteTailAsDifference : ∀ n →
      (prefix≤n : prefixLength ℕ.≤ n) →
      partialSum (dropSeries prefixLength (Abs.absℝ ∘ a))
          (n ∸ prefixLength) ≡
      partialSum (Abs.absℝ ∘ a) n Group.-
        partialSum (Abs.absℝ ∘ a) prefixLength
    absoluteTailAsDifference n prefix≤n =
      partialSum-drop prefixLength (Abs.absℝ ∘ a)
        (n ∸ prefixLength)
      ∙ cong
          (Group._- partialSum (Abs.absℝ ∘ a) prefixLength)
          (cong (partialSum (Abs.absℝ ∘ a))
            (ℕ.[n-m]+m prefixLength n prefix≤n))

    absoluteTailBound : ∀ n →
      (index≤n : mertensIndex ℕ.≤ n) →
      partialSum (dropSeries prefixLength (Abs.absℝ ∘ a))
          (n ∸ prefixLength) <ℝ
      Real.ιℚ (fst (tailRadius ε))
    absoluteTailBound n index≤n =
      subst (_<ℝ Real.ιℚ (fst (tailRadius ε)))
        (sym (absoluteTailAsDifference n prefix≤n))
        (≤<ℝ-trans
          difference (Abs.absℝ difference)
          (Real.ιℚ (fst (tailRadius ε)))
          (x≤abs difference)
          (closeness→absDifference<
            (partialSum (Abs.absℝ ∘ a) n)
            (partialSum (Abs.absℝ ∘ a) prefixLength)
            (tailRadius ε)
            (snd a-tail n prefixLength prefix≤n ℕ.≤-refl)))
      where
      prefix≤n : prefixLength ℕ.≤ n
      prefix≤n = prefixLength≤index n index≤n

      difference : Real.ℝ
      difference =
        partialSum (Abs.absℝ ∘ a) n Group.-
          partialSum (Abs.absℝ ∘ a) prefixLength

    tailMajorantBound : ∀ n →
      mertensIndex ℕ.≤ n →
      partialSum
        (dropSeries prefixLength
          (cauchyProductRemainderMajorant a b n))
        (n ∸ prefixLength) <ℝ
      Real.ιℚ (fst (ε /4₊))
    tailMajorantBound n index≤n =
      ≤<ℝ-trans
        (partialSum
          (dropSeries prefixLength
            (cauchyProductRemainderMajorant a b n))
          (n ∸ prefixLength))
        (partialSum scaledAbsoluteTail (n ∸ prefixLength))
        (Real.ιℚ (fst (ε /4₊)))
        (partialSumMono
          (dropSeries prefixLength
            (cauchyProductRemainderMajorant a b n))
          scaledAbsoluteTail
          (tailTermBound n)
          (n ∸ prefixLength))
        scaledAbsoluteTailBound
      where
      absoluteTail : RealSequence
      absoluteTail =
        dropSeries prefixLength (Abs.absℝ ∘ a)

      scaledAbsoluteTail : RealSequence
      scaledAbsoluteTail j =
        absoluteTail j Mul.· Real.ιℚ (fst doubleB)

      doubleBPositive : zeroℝ <ℝ Real.ιℚ (fst doubleB)
      doubleBPositive =
        <ℚ→<ℝ 0 (fst doubleB) (snd doubleB)

      scaledProductBound :
        partialSum absoluteTail (n ∸ prefixLength) Mul.·
            Real.ιℚ (fst doubleB) <ℝ
        Real.ιℚ (fst (tailRadius ε)) Mul.·
            Real.ιℚ (fst doubleB)
      scaledProductBound =
        mul-preserves≪-right-positive
          (partialSum absoluteTail (n ∸ prefixLength))
          (Real.ιℚ (fst (tailRadius ε)))
          (Real.ιℚ (fst doubleB))
          (absoluteTailBound n index≤n)
          doubleBPositive

      rationalProductPath :
        Real.ιℚ (fst (tailRadius ε)) Mul.·
          Real.ιℚ (fst doubleB) ≡
        Real.ιℚ (fst (ε /4₊))
      rationalProductPath =
        Mul.mul-ι-ι (fst (tailRadius ε)) (fst doubleB)
        ∙ cong Real.ιℚ
            (ℚ.·Comm (fst (tailRadius ε)) (fst doubleB)
            ∙ ·／ doubleB (ε /4₊))

      scaledAbsoluteTailBound :
        partialSum scaledAbsoluteTail (n ∸ prefixLength) <ℝ
        Real.ιℚ (fst (ε /4₊))
      scaledAbsoluteTailBound =
        subst2 _<ℝ_
          (sym
            (partialSum-right-scale absoluteTail
              (Real.ιℚ (fst doubleB))
              (n ∸ prefixLength)))
          rationalProductPath scaledProductBound

    fullMajorantBound : ∀ n →
      mertensIndex ℕ.≤ n →
      partialSum (cauchyProductRemainderMajorant a b n) n <ℝ
      Real.ιℚ (fst ε)
    fullMajorantBound n index≤n =
      <ℝ-trans
        (partialSum (cauchyProductRemainderMajorant a b n) n)
        (Real.ιℚ (fst (ε /2₊)))
        (Real.ιℚ (fst ε))
        majorantLessThanHalf
        (<ℚ→<ℝ
          (fst (ε /2₊)) (fst ε) (/2₊<id ε))
      where
      prefix≤n : prefixLength ℕ.≤ n
      prefix≤n = prefixLength≤index n index≤n

      splitPath :
        partialSum (cauchyProductRemainderMajorant a b n) n ≡
        partialSum (cauchyProductRemainderMajorant a b n)
            prefixLength Add.+
        partialSum
          (dropSeries prefixLength
            (cauchyProductRemainderMajorant a b n))
          (n ∸ prefixLength)
      splitPath =
        partialSum-splitAt
          (cauchyProductRemainderMajorant a b n)
          prefixLength n prefix≤n

      quarterSumPath :
        Real.ιℚ (fst (ε /4₊)) Add.+
          Real.ιℚ (fst (ε /4₊)) ≡
        Real.ιℚ (fst (ε /2₊))
      quarterSumPath =
        Add.add-ι-ι (fst (ε /4₊)) (fst (ε /4₊))
        ∙ cong Real.ιℚ (/4+/4≡/2 (fst ε))

      splitBound :
        partialSum (cauchyProductRemainderMajorant a b n)
            prefixLength Add.+
        partialSum
          (dropSeries prefixLength
            (cauchyProductRemainderMajorant a b n))
          (n ∸ prefixLength) <ℝ
        Real.ιℚ (fst (ε /4₊)) Add.+
          Real.ιℚ (fst (ε /4₊))
      splitBound =
        ≤<ℝ-add
          (partialSum (cauchyProductRemainderMajorant a b n)
            prefixLength)
          (Real.ιℚ (fst (ε /4₊)))
          (partialSum
            (dropSeries prefixLength
              (cauchyProductRemainderMajorant a b n))
            (n ∸ prefixLength))
          (Real.ιℚ (fst (ε /4₊)))
          (prefixMajorantBound n index≤n)
          (tailMajorantBound n index≤n)

      majorantLessThanHalf :
        partialSum (cauchyProductRemainderMajorant a b n) n <ℝ
        Real.ιℚ (fst (ε /2₊))
      majorantLessThanHalf =
        subst2 _<ℝ_ (sym splitPath) quarterSumPath splitBound

    fullRemainderBound : ∀ n →
      mertensIndex ℕ.≤ n →
      Abs.absℝ (cauchyProductRemainder a b n) <ℝ
      Real.ιℚ (fst ε)
    fullRemainderBound n index≤n =
      ≤<ℝ-trans
        (Abs.absℝ (cauchyProductRemainder a b n))
        (partialSum (cauchyProductRemainderMajorant a b n) n)
        (Real.ιℚ (fst ε))
        (cauchyProductRemainderAbsBound a b n)
        (fullMajorantBound n index≤n)

    mertensRemainderTail :
      Σ[ N ∈ ℕ ]
        (∀ n → N ℕ.≤ n →
          cauchyProductRemainder a b n
            Real.Base.≈ᶜ[ ε ] zeroℝ)
    mertensRemainderTail =
      mertensIndex
      , λ n index≤n →
          absDifference<→closeness
            (cauchyProductRemainder a b n) zeroℝ ε
            (subst (_<ℝ Real.ιℚ (fst ε))
              (sym
                (cong Abs.absℝ
                  (sub-zero-right
                    (cauchyProductRemainder a b n))))
              (fullRemainderBound n index≤n))


-- Each requested radius opens exactly two truncated tails and returns one
-- truncated remainder cutoff.  No function choosing cutoffs at all radii is
-- ever assembled.

mertensRemainderVanishes : ∀ A B a b →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  CauchyProductRemainderVanishes a b
mertensRemainderVanishes
  A B a b a-absolute-bounded b-bounded
  a-absolute-cauchy b-cauchy ε =
  PT.rec2 squash₁
    (λ a-tail b-tail →
      ∣ mertensRemainderTail
          A B a b a-absolute-bounded b-bounded
          ε a-tail b-tail ∣₁)
    (a-absolute-cauchy
      (tailRadius A B a b a-absolute-bounded b-bounded ε))
    (b-cauchy
      (prefixRadius A B a b a-absolute-bounded b-bounded ε))


mertensRectangularApproximation : ∀ A B a b →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  CauchyProductRectangularApproximation a b
mertensRectangularApproximation
  A B a b a-absolute-bounded b-bounded
  a-absolute-cauchy b-cauchy =
  remainderVanishes→rectangularApproximation a b
    (mertensRemainderVanishes
      A B a b a-absolute-bounded b-bounded
      a-absolute-cauchy b-cauchy)


mertensCauchyProductIsCauchy : ∀ A B a b →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  IsCauchySeries (cauchyProduct a b)
mertensCauchyProductIsCauchy
  A B a b a-absolute-bounded b-bounded
  a-absolute-cauchy b-cauchy =
  cauchyProductIsCauchy a b
    (absoluteCauchySeriesIsCauchy a a-absolute-cauchy)
    b-cauchy
    (mertensRectangularApproximation
      A B a b a-absolute-bounded b-bounded
      a-absolute-cauchy b-cauchy)


mertensCauchyProductSummable : ∀ A B a b →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  Summable (cauchyProduct a b)
mertensCauchyProductSummable
  A B a b a-absolute-bounded b-bounded
  a-summable b-summable a-absolute-cauchy b-cauchy =
  cauchyProductSummable a b a-summable b-summable
    (mertensRectangularApproximation
      A B a b a-absolute-bounded b-bounded
      a-absolute-cauchy b-cauchy)


mertensSeriesSum-cauchyProduct : ∀ A B a b →
  (a-absolute-bounded : UniformAbsolutePartialSumBound A a) →
  (b-bounded : UniformPartialSumAbsBound B b) →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  (product-summable : Summable (cauchyProduct a b)) →
  (a-absolute-cauchy : IsAbsolutelyCauchySeries a) →
  (b-cauchy : IsCauchySeries b) →
  seriesSum (cauchyProduct a b) product-summable ≡
  seriesSum a a-summable Mul.· seriesSum b b-summable
mertensSeriesSum-cauchyProduct
  A B a b a-absolute-bounded b-bounded
  a-summable b-summable product-summable
  a-absolute-cauchy b-cauchy =
  seriesSum-cauchyProduct a b
    a-summable b-summable product-summable
    (mertensRectangularApproximation
      A B a b a-absolute-bounded b-bounded
      a-absolute-cauchy b-cauchy)

module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.ConvolutionAbsolute where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (mul-monotone-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Order
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Bounds
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Convolution
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.ConvolutionMertens


absoluteTerms-idempotent : ∀ (terms : RealSequence) →
  (Abs.absℝ ∘ (Abs.absℝ ∘ terms)) ≡
  (Abs.absℝ ∘ terms)
absoluteTerms-idempotent terms =
  funExt (λ n → Abs.absℝ-idempotent (terms n))


absoluteSequenceIsAbsolutelyCauchy : ∀ (terms : RealSequence) →
  IsAbsolutelyCauchySeries terms →
  IsAbsolutelyCauchySeries (Abs.absℝ ∘ terms)
absoluteSequenceIsAbsolutelyCauchy terms absolute =
  subst IsCauchySeries
    (sym (absoluteTerms-idempotent terms)) absolute


-- Absolute convergence supplies merely some rational sum bounds.  Since
-- rectangular approximation is a proposition, both bounds can be opened
-- locally and discarded again; callers never choose them.

absoluteMertensRectangularApproximation : ∀ (a b : RealSequence) →
  IsAbsolutelyCauchySeries a →
  IsAbsolutelyCauchySeries b →
  CauchyProductRectangularApproximation a b
absoluteMertensRectangularApproximation a b a-absolute b-absolute =
  PT.rec2
    (isPropEventuallyClose
      (λ n → partialSum a n Mul.· partialSum b n)
      (partialSum (cauchyProduct a b)))
    with-bounds
    (mereAbsoluteCauchySeriesSumBound a a-absolute)
    (mereAbsoluteCauchySeriesSumBound b b-absolute)
  where
  with-bounds :
    (Σ[ A ∈ ℚ₊ ] AbsoluteCauchySeriesSumBound A a a-absolute) →
    (Σ[ B ∈ ℚ₊ ] AbsoluteCauchySeriesSumBound B b b-absolute) →
    CauchyProductRectangularApproximation a b
  with-bounds (A , a-sum-bound) (B , b-sum-bound) =
    mertensRectangularApproximation A B a b
      (absoluteCauchySumBound→uniformAbsoluteBound
        A a a-absolute a-sum-bound)
      (uniformAbsoluteBound→uniformBound B b
        (absoluteCauchySumBound→uniformAbsoluteBound
          B b b-absolute b-sum-bound))
      a-absolute
      (absoluteCauchySeriesIsCauchy b b-absolute)


absoluteMertensCauchyProductIsCauchy : ∀ (a b : RealSequence) →
  IsAbsolutelyCauchySeries a →
  IsAbsolutelyCauchySeries b →
  IsCauchySeries (cauchyProduct a b)
absoluteMertensCauchyProductIsCauchy a b a-absolute b-absolute =
  cauchyProductIsCauchy a b
    (absoluteCauchySeriesIsCauchy a a-absolute)
    (absoluteCauchySeriesIsCauchy b b-absolute)
    (absoluteMertensRectangularApproximation
      a b a-absolute b-absolute)


absoluteMertensCauchyProductIsAbsolutelyCauchy : ∀ (a b : RealSequence) →
  IsAbsolutelyCauchySeries a →
  IsAbsolutelyCauchySeries b →
  IsAbsolutelyCauchySeries (cauchyProduct a b)
absoluteMertensCauchyProductIsAbsolutelyCauchy
  a b a-absolute b-absolute =
  absoluteCauchyProductFromMajorant a b
    (absoluteMertensCauchyProductIsCauchy
      (Abs.absℝ ∘ a) (Abs.absℝ ∘ b)
      (absoluteSequenceIsAbsolutelyCauchy a a-absolute)
      (absoluteSequenceIsAbsolutelyCauchy b b-absolute))


absoluteMertensCauchyProductSummable : ∀ (a b : RealSequence) →
  IsAbsolutelyCauchySeries a →
  IsAbsolutelyCauchySeries b →
  Summable (cauchyProduct a b)
absoluteMertensCauchyProductSummable a b a-absolute b-absolute =
  absoluteCauchySeriesIsSummable (cauchyProduct a b)
    (absoluteMertensCauchyProductIsAbsolutelyCauchy
      a b a-absolute b-absolute)


absoluteMertensCauchyProductAbsolutelySummable : ∀ (a b : RealSequence) →
  IsAbsolutelyCauchySeries a →
  IsAbsolutelyCauchySeries b →
  AbsolutelySummable (cauchyProduct a b)
absoluteMertensCauchyProductAbsolutelySummable
  a b a-absolute b-absolute =
  absoluteCauchySeriesIsAbsolutelySummable (cauchyProduct a b)
    (absoluteMertensCauchyProductIsAbsolutelyCauchy
      a b a-absolute b-absolute)


absoluteMertensSeriesSum-cauchyProduct : ∀ (a b : RealSequence)
  (a-summable : Summable a)
  (b-summable : Summable b)
  (product-summable : Summable (cauchyProduct a b)) →
  IsAbsolutelyCauchySeries a →
  IsAbsolutelyCauchySeries b →
  seriesSum (cauchyProduct a b) product-summable ≡
  seriesSum a a-summable Mul.· seriesSum b b-summable
absoluteMertensSeriesSum-cauchyProduct
  a b a-summable b-summable product-summable
  a-absolute b-absolute =
  seriesSum-cauchyProduct a b
    a-summable b-summable product-summable
    (absoluteMertensRectangularApproximation
      a b a-absolute b-absolute)


-- Seal the large radiuswise constructions before quantitative clients use
-- them.  This is a checking-performance boundary, not an extra axiom.

opaque
  absoluteMertensRectangularApproximation-sealed :
    ∀ (a b : RealSequence) →
    IsAbsolutelyCauchySeries a →
    IsAbsolutelyCauchySeries b →
    CauchyProductRectangularApproximation a b
  absoluteMertensRectangularApproximation-sealed =
    absoluteMertensRectangularApproximation

  absoluteMertensCauchyProductIsAbsolutelyCauchy-sealed :
    ∀ (a b : RealSequence) →
    IsAbsolutelyCauchySeries a →
    IsAbsolutelyCauchySeries b →
    IsAbsolutelyCauchySeries (cauchyProduct a b)
  absoluteMertensCauchyProductIsAbsolutelyCauchy-sealed =
    absoluteMertensCauchyProductIsAbsolutelyCauchy


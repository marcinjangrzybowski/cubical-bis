module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat using (zero ; suc)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (add-monotone ; abs-triangle)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (closeness→absDifference< ; absDifference<→closeness)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (≤<ℝ-trans)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.FiniteSum
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.FiniteModification


absolutePartialSum : RealSequence → RealSequence
absolutePartialSum terms =
  partialSum (Abs.absℝ ∘ terms)


IsAbsolutelyCauchySeries : RealSequence → Type₀
IsAbsolutelyCauchySeries terms =
  IsCauchySeries (Abs.absℝ ∘ terms)


AbsolutelySummable : RealSequence → Type₀
AbsolutelySummable terms =
  Summable (Abs.absℝ ∘ terms)


isAbsolutelyCauchySeries≃absolutelySummable : ∀ terms →
  IsAbsolutelyCauchySeries terms ≃ AbsolutelySummable terms
isAbsolutelyCauchySeries≃absolutelySummable terms =
  isCauchySeries≃summable (Abs.absℝ ∘ terms)


absoluteCauchySeriesIsAbsolutelySummable : ∀ terms →
  IsAbsolutelyCauchySeries terms → AbsolutelySummable terms
absoluteCauchySeriesIsAbsolutelySummable terms =
  cauchySeriesIsSummable (Abs.absℝ ∘ terms)


absolutelySummableIsAbsolutelyCauchy : ∀ terms →
  AbsolutelySummable terms → IsAbsolutelyCauchySeries terms
absolutelySummableIsAbsolutelyCauchy terms =
  summableIsCauchySeries (Abs.absℝ ∘ terms)


seriesSumAbsBound : ∀ terms →
  (summable : Summable terms) →
  (absolute-summable : AbsolutelySummable terms) →
  Abs.absℝ (seriesSum terms summable) ≤ℝ
  seriesSum (Abs.absℝ ∘ terms) absolute-summable
seriesSumAbsBound terms summable absolute-summable =
  pointwiseLePresLimits
    (partialSumAbsBound terms)
    (absPresIsLimitSequence
      (seriesSumHasSum terms summable))
    (seriesSumHasSum
      (Abs.absℝ ∘ terms) absolute-summable)


-- The regular-real development only exposed this Cauchy result for a
-- rational scalar.  Here it holds for every real scalar: multiplication of
-- native Cauchy sequences is already available, and `abs-mul` identifies
-- the corresponding absolute-value partial sums.

scaleSeriesIsAbsolutelyCauchy : ∀ c terms →
  IsAbsolutelyCauchySeries terms →
  IsAbsolutelyCauchySeries (scaleSeries c terms)
scaleSeriesIsAbsolutelyCauchy c terms absolute =
  eventuallyEqualSeriesPresIsCauchy
    ∣ 0 , (λ n _ → sym (abs-mul c (terms n))) ∣₁
    (scaleSeriesIsCauchy
      (Abs.absℝ c) (Abs.absℝ ∘ terms) absolute)


scaleSeriesIsAbsolutelySummable : ∀ c terms →
  AbsolutelySummable terms →
  AbsolutelySummable (scaleSeries c terms)
scaleSeriesIsAbsolutelySummable c terms absolute-summable =
  absoluteCauchySeriesIsAbsolutelySummable
    (scaleSeries c terms)
    (scaleSeriesIsAbsolutelyCauchy c terms
      (absolutelySummableIsAbsolutelyCauchy
        terms absolute-summable))


-- Domination is formulated directly for the radiuswise Cauchy predicate.
-- Eliminating its tail witness uses only `PT.map`: no modulus function is
-- chosen.  Metric/order compatibility converts the order estimate back to
-- primitive closeness at the same requested radius.

dominatedCauchySeriesIsCauchy :
  (terms bound : RealSequence) →
  (∀ n → Abs.absℝ (terms n) ≤ℝ bound n) →
  IsCauchySeries bound →
  IsCauchySeries terms
dominatedCauchySeriesIsCauchy
  terms bound dominates bound-cauchy ε =
  PT.map makeTail (bound-cauchy ε)
  where
  makeTail : CauchyTail (partialSum bound) ε →
    CauchyTail (partialSum terms) ε
  makeTail (N , closeBound) =
    N , λ m n N≤m N≤n →
      absDifference<→closeness
        (partialSum terms m) (partialSum terms n) ε
        (≤<ℝ-trans
          (Abs.absℝ
            (partialSum terms m Group.- partialSum terms n))
          (Abs.absℝ
            (partialSum bound m Group.- partialSum bound n))
          (Real.ιℚ (fst ε))
          (partialSumDistanceBoundBy
            terms bound dominates m n)
          (closeness→absDifference<
            (partialSum bound m) (partialSum bound n) ε
            (closeBound m n N≤m N≤n)))


dominatedCauchySeriesIsSummable :
  (terms bound : RealSequence) →
  (∀ n → Abs.absℝ (terms n) ≤ℝ bound n) →
  IsCauchySeries bound →
  Summable terms
dominatedCauchySeriesIsSummable terms bound dominates bound-cauchy =
  cauchySeriesIsSummable terms
    (dominatedCauchySeriesIsCauchy
      terms bound dominates bound-cauchy)


absoluteCauchySeriesIsCauchy : ∀ terms →
  IsAbsolutelyCauchySeries terms →
  IsCauchySeries terms
absoluteCauchySeriesIsCauchy terms =
  dominatedCauchySeriesIsCauchy
    terms (Abs.absℝ ∘ terms)
    (λ n → ≤ℝ-refl (Abs.absℝ (terms n)))


absoluteCauchySeriesIsSummable : ∀ terms →
  IsAbsolutelyCauchySeries terms →
  Summable terms
absoluteCauchySeriesIsSummable terms absolute =
  cauchySeriesIsSummable terms
    (absoluteCauchySeriesIsCauchy terms absolute)


absolutelySummableIsSummable : ∀ terms →
  AbsolutelySummable terms → Summable terms
absolutelySummableIsSummable terms absolute-summable =
  absoluteCauchySeriesIsSummable terms
    (absolutelySummableIsAbsolutelyCauchy terms absolute-summable)


absoluteCauchySeriesSumAbsBound :
  (terms : RealSequence) →
  (absolute : IsAbsolutelyCauchySeries terms) →
  Abs.absℝ
    (seriesSum terms
      (absoluteCauchySeriesIsSummable terms absolute)) ≤ℝ
  seriesSum (Abs.absℝ ∘ terms)
    (absoluteCauchySeriesIsAbsolutelySummable terms absolute)
absoluteCauchySeriesSumAbsBound terms absolute =
  seriesSumAbsBound
    terms
    (absoluteCauchySeriesIsSummable terms absolute)
    (absoluteCauchySeriesIsAbsolutelySummable terms absolute)

module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (RationalBound ; ∃rationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Order
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.FiniteSum
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute


UniformPartialSumAbsBound : ℚ₊ → RealSequence → Type₀
UniformPartialSumAbsBound B terms =
  ∀ n → Abs.absℝ (partialSum terms n) ≤ℝ
    Real.ιℚ (fst B)


UniformAbsolutePartialSumBound : ℚ₊ → RealSequence → Type₀
UniformAbsolutePartialSumBound B terms =
  ∀ n → partialSum (Abs.absℝ ∘ terms) n ≤ℝ
    Real.ιℚ (fst B)


uniformAbsoluteBound→uniformBound : ∀ B terms →
  UniformAbsolutePartialSumBound B terms →
  UniformPartialSumAbsBound B terms
uniformAbsoluteBound→uniformBound B terms absolute-bounded n =
  ≤ℝ-trans
    (Abs.absℝ (partialSum terms n))
    (partialSum (Abs.absℝ ∘ terms) n)
    (Real.ιℚ (fst B))
    (partialSumAbsBound terms n)
    (absolute-bounded n)


absolutePartialSumLeSeriesSum : ∀ terms →
  (absolute-summable : AbsolutelySummable terms) →
  ∀ n →
  partialSum (Abs.absℝ ∘ terms) n ≤ℝ
  seriesSum (Abs.absℝ ∘ terms) absolute-summable
absolutePartialSumLeSeriesSum terms absolute-summable =
  partialSumLeSeriesSum
    (Abs.absℝ ∘ terms) absolute-summable
    (λ n → zero≤abs (terms n))


absoluteSeriesSumBound→uniformAbsoluteBound : ∀ B terms →
  (absolute-summable : AbsolutelySummable terms) →
  seriesSum (Abs.absℝ ∘ terms) absolute-summable ≤ℝ
    Real.ιℚ (fst B) →
  UniformAbsolutePartialSumBound B terms
absoluteSeriesSumBound→uniformAbsoluteBound
  B terms absolute-summable sum-bounded n =
  ≤ℝ-trans
    (partialSum (Abs.absℝ ∘ terms) n)
    (seriesSum (Abs.absℝ ∘ terms) absolute-summable)
    (Real.ιℚ (fst B))
    (absolutePartialSumLeSeriesSum terms absolute-summable n)
    sum-bounded


AbsoluteCauchySeriesSumBound :
  ℚ₊ → (terms : RealSequence) →
  IsAbsolutelyCauchySeries terms → Type₀
AbsoluteCauchySeriesSumBound B terms absolute =
  seriesSum (Abs.absℝ ∘ terms)
      (absoluteCauchySeriesIsAbsolutelySummable terms absolute) ≤ℝ
    Real.ιℚ (fst B)


absoluteCauchySumBound→uniformAbsoluteBound : ∀ B terms absolute →
  AbsoluteCauchySeriesSumBound B terms absolute →
  UniformAbsolutePartialSumBound B terms
absoluteCauchySumBound→uniformAbsoluteBound B terms absolute =
  absoluteSeriesSumBound→uniformAbsoluteBound B terms
    (absoluteCauchySeriesIsAbsolutelySummable terms absolute)


-- A global rational bound is useful data, but choosing one is unnecessary
-- for proposition-valued applications.  Archimedeanness supplies merely one
-- bound for the uniquely determined absolute sum, which can be eliminated
-- directly into those applications.

mereAbsoluteCauchySeriesSumBound : ∀ terms absolute →
  ∥ Σ[ B ∈ ℚ₊ ] AbsoluteCauchySeriesSumBound B terms absolute ∥₁
mereAbsoluteCauchySeriesSumBound terms absolute =
  PT.map toSumBound (∃rationalBound absolute-sum)
  where
  absolute-sum : Real.ℝ
  absolute-sum =
    seriesSum (Abs.absℝ ∘ terms)
      (absoluteCauchySeriesIsAbsolutelySummable terms absolute)

  toSumBound : RationalBound absolute-sum →
    Σ[ B ∈ ℚ₊ ] AbsoluteCauchySeriesSumBound B terms absolute
  toSumBound (B , abs-sum≤B) =
    B , ≤ℝ-trans absolute-sum (Abs.absℝ absolute-sum)
      (Real.ιℚ (fst B)) (x≤abs absolute-sum) abs-sum≤B

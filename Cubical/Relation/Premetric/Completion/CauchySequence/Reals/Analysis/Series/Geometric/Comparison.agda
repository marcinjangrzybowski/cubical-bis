module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Density
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Rational
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Convergence


private
  oneℝ : Real.ℝ
  oneℝ = CommRingStr.1r (snd ℝCommRing)


-- An exhibited rational contraction is often more usable constructively
-- than the bare open inequality |x| < 1: it provides the rational geometric
-- series which will majorize the target, while still carrying no modulus.

RationalContractionBound : Real.ℝ → Type₀
RationalContractionBound x =
  Σ[ q ∈ ℚ₊ ]
    (Abs.absℝ x <ℝ Real.ιℚ (fst q)) ×
    (fst q ℚ.< 1)


rationalContractionBoundWithin : ∀ x radius →
  Abs.absℝ x ≤ℝ radius →
  RationalContractionBound radius →
  RationalContractionBound x
rationalContractionBoundWithin
  x radius absx≤radius (q , radius<q , q<1) =
  q
  , ≤<ℝ-trans
      (Abs.absℝ x) (Abs.absℝ radius) (Real.ιℚ (fst q))
      (≤ℝ-trans
        (Abs.absℝ x) radius (Abs.absℝ radius)
        absx≤radius (x≤abs radius))
      radius<q
  , q<1


rationalContractionBound→abs<1 : ∀ x →
  RationalContractionBound x →
  Abs.absℝ x <ℝ oneℝ
rationalContractionBound→abs<1
  x (q , absx<q , q<1) =
  <ℝ-trans
    (Abs.absℝ x) (Real.ιℚ (fst q)) oneℝ
    absx<q (<ℚ→<ℝ (fst q) 1 q<1)


rationalContractionBound→x<1 : ∀ x →
  RationalContractionBound x →
  x <ℝ oneℝ
rationalContractionBound→x<1 x bound =
  ≤<ℝ-trans x (Abs.absℝ x) oneℝ
    (x≤abs x)
    (rationalContractionBound→abs<1 x bound)


geometricSeriesIsAbsolutelyCauchyByRationalBound : ∀ x →
  (bound : RationalContractionBound x) →
  IsCauchySeries
    (geometricTerms (Real.ιℚ (fst (fst bound)))) →
  IsAbsolutelyCauchySeries (geometricTerms x)
geometricSeriesIsAbsolutelyCauchyByRationalBound
  x (q , absx<q , q<1) rational-series-cauchy =
  dominatedCauchySeriesIsCauchy
    (Abs.absℝ ∘ geometricTerms x)
    (geometricTerms (Real.ιℚ (fst q)))
    dominates rational-series-cauchy
  where
  absx≤q : Abs.absℝ x ≤ℝ Real.ιℚ (fst q)
  absx≤q =
    <ℝ-weaken (Abs.absℝ x) (Real.ιℚ (fst q)) absx<q

  dominates : ∀ n →
    Abs.absℝ (Abs.absℝ (x ^ⁿ n)) ≤ℝ
    Real.ιℚ (fst q) ^ⁿ n
  dominates n =
    subst (_≤ℝ Real.ιℚ (fst q) ^ⁿ n)
      (sym (Abs.absℝ-idempotent (x ^ⁿ n) ∙ absPow n x))
      (powMono n (zero≤abs x) absx≤q)


geometricSeriesIsCauchyByRationalBound : ∀ x →
  (bound : RationalContractionBound x) →
  IsCauchySeries
    (geometricTerms (Real.ιℚ (fst (fst bound)))) →
  IsCauchySeries (geometricTerms x)
geometricSeriesIsCauchyByRationalBound x bound rational-series-cauchy =
  absoluteCauchySeriesIsCauchy (geometricTerms x)
    (geometricSeriesIsAbsolutelyCauchyByRationalBound
      x bound rational-series-cauchy)


geometricSeriesIsSummableByRationalBound : ∀ x →
  (bound : RationalContractionBound x) →
  IsCauchySeries
    (geometricTerms (Real.ιℚ (fst (fst bound)))) →
  Summable (geometricTerms x)
geometricSeriesIsSummableByRationalBound x bound rational-series-cauchy =
  absoluteCauchySeriesIsSummable (geometricTerms x)
    (geometricSeriesIsAbsolutelyCauchyByRationalBound
      x bound rational-series-cauchy)


geometricSeriesHasSumByRationalBound : ∀ x →
  (bound : RationalContractionBound x) →
  IsCauchySeries
    (geometricTerms (Real.ιℚ (fst (fst bound)))) →
  HasSum (geometricTerms x)
    (positiveReciprocal
      (oneℝ Group.- x)
      (strictlyPositiveDifference≪ x oneℝ
        (rationalContractionBound→x<1 x bound)))
geometricSeriesHasSumByRationalBound x bound rational-series-cauchy =
  geometricSeriesHasSum x x<1
    (summableTermsTendToZero (geometricTerms x)
      (geometricSeriesIsSummableByRationalBound
        x bound rational-series-cauchy))
  where
  x<1 : x <ℝ oneℝ
  x<1 = rationalContractionBound→x<1 x bound


positiveRationalGeometricSeriesIsCauchy : ∀ q →
  fst q ℚ.< 1 →
  IsCauchySeries (geometricTerms (Real.ιℚ (fst q)))
positiveRationalGeometricSeriesIsCauchy q q<1 =
  summableIsCauchySeries (geometricTerms (Real.ιℚ (fst q)))
    (rationalGeometricSeriesSummable
      (fst q) (ℚ.<Weaken≤ 0 (fst q) (snd q)) q<1)


geometricSeriesIsAbsolutelyCauchyByRationalContraction : ∀ x →
  RationalContractionBound x →
  IsAbsolutelyCauchySeries (geometricTerms x)
geometricSeriesIsAbsolutelyCauchyByRationalContraction x bound =
  geometricSeriesIsAbsolutelyCauchyByRationalBound x bound
    (positiveRationalGeometricSeriesIsCauchy
      (fst bound) (snd (snd bound)))


geometricSeriesIsCauchyByRationalContraction : ∀ x →
  RationalContractionBound x →
  IsCauchySeries (geometricTerms x)
geometricSeriesIsCauchyByRationalContraction x bound =
  absoluteCauchySeriesIsCauchy (geometricTerms x)
    (geometricSeriesIsAbsolutelyCauchyByRationalContraction x bound)


geometricSeriesIsSummableByRationalContraction : ∀ x →
  RationalContractionBound x →
  Summable (geometricTerms x)
geometricSeriesIsSummableByRationalContraction x bound =
  absoluteCauchySeriesIsSummable (geometricTerms x)
    (geometricSeriesIsAbsolutelyCauchyByRationalContraction x bound)


geometricSeriesHasSumByRationalContraction : ∀ x →
  (bound : RationalContractionBound x) →
  HasSum (geometricTerms x)
    (positiveReciprocal
      (oneℝ Group.- x)
      (strictlyPositiveDifference≪ x oneℝ
        (rationalContractionBound→x<1 x bound)))
geometricSeriesHasSumByRationalContraction x bound =
  geometricSeriesHasSumByRationalBound x bound
    (positiveRationalGeometricSeriesIsCauchy
      (fst bound) (snd (snd bound)))


-- The rational witness is convenient data, but it is not necessary in a
-- proposition-valued conclusion.  Order density produces it merely, and the
-- surrounding Cauchy/summability propositions permit exactly that
-- truncation elimination.  Thus the user-facing convergence criterion can
-- retain the sharp hypothesis |x| < 1.

abs<1→mereRationalContractionBound : ∀ x →
  Abs.absℝ x <ℝ oneℝ →
  ∥ RationalContractionBound x ∥₁
abs<1→mereRationalContractionBound x absx<1 =
  PT.map makeBound (denseℚinℝ (Abs.absℝ x) oneℝ absx<1)
  where
  makeBound :
    Σ[ q ∈ ℚ.ℚ ]
      (Abs.absℝ x <ℝ Real.ιℚ q) ×
      (Real.ιℚ q <ℝ oneℝ) →
    RationalContractionBound x
  makeBound (q , absx<q , q<1-real) =
    (q , q-positive) , absx<q , q<1
    where
    zero<q-real : Real.ιℚ 0 <ℝ Real.ιℚ q
    zero<q-real =
      ≤<ℝ-trans (Real.ιℚ 0) (Abs.absℝ x) (Real.ιℚ q)
        (zero≤abs x) absx<q

    q-positive : 0 ℚ.< q
    q-positive = <ℝ→<ℚ 0 q zero<q-real

    q<1 : q ℚ.< 1
    q<1 = <ℝ→<ℚ q 1 q<1-real


geometricSeriesIsAbsolutelyCauchyOfAbs<1 : ∀ x →
  Abs.absℝ x <ℝ oneℝ →
  IsAbsolutelyCauchySeries (geometricTerms x)
geometricSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1 =
  PT.rec
    (isPropIsCauchySeries (Abs.absℝ ∘ geometricTerms x))
    (geometricSeriesIsAbsolutelyCauchyByRationalContraction x)
    (abs<1→mereRationalContractionBound x absx<1)


geometricSeriesIsCauchyOfAbs<1 : ∀ x →
  Abs.absℝ x <ℝ oneℝ →
  IsCauchySeries (geometricTerms x)
geometricSeriesIsCauchyOfAbs<1 x absx<1 =
  absoluteCauchySeriesIsCauchy (geometricTerms x)
    (geometricSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1)


geometricSeriesIsSummableOfAbs<1 : ∀ x →
  Abs.absℝ x <ℝ oneℝ →
  Summable (geometricTerms x)
geometricSeriesIsSummableOfAbs<1 x absx<1 =
  absoluteCauchySeriesIsSummable (geometricTerms x)
    (geometricSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1)


geometricSeriesHasSumOfAbs<1 : ∀ x →
  (absx<1 : Abs.absℝ x <ℝ oneℝ) →
  HasSum (geometricTerms x)
    (positiveReciprocal
      (oneℝ Group.- x)
      (strictlyPositiveDifference≪ x oneℝ
        (≤<ℝ-trans x (Abs.absℝ x) oneℝ (x≤abs x) absx<1)))
geometricSeriesHasSumOfAbs<1 x absx<1 =
  geometricSeriesHasSum x x<1
    (summableTermsTendToZero (geometricTerms x)
      (geometricSeriesIsSummableOfAbs<1 x absx<1))
  where
  x<1 : x <ℝ oneℝ
  x<1 = ≤<ℝ-trans x (Abs.absℝ x) oneℝ (x≤abs x) absx<1

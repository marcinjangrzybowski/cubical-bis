module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Convergence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_ ; <ℝ-weaken)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Rational
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant


private
  oneℝ : Real.ℝ
  oneℝ = CommRingStr.1r (snd ℝCommRing)


coefficientGeometricMajorant : ℚ₊ → ℚ₊ → RealSequence
coefficientGeometricMajorant C q =
  scaleSeries (Real.ιℚ (fst C))
    (geometricTerms (Real.ιℚ (fst q)))


constantCoefficientMajorant : ℚ₊ → RealSequence
constantCoefficientMajorant C _ = Real.ιℚ (fst C)


coefficientGeometricMajorantPath : ∀ C q →
  powerSeriesTerms (constantCoefficientMajorant C)
    (Real.ιℚ (fst q)) ≡
  coefficientGeometricMajorant C q
coefficientGeometricMajorantPath C q = refl


coefficientAbsBoundIsMajorized : ∀ C coefficients →
  CoefficientAbsBound C coefficients →
  CoefficientMajorizedBy coefficients
    (constantCoefficientMajorant C)
coefficientAbsBoundIsMajorized C coefficients bounded = bounded


powerSeriesTermAbsBound : ∀ C q coefficients x →
  CoefficientAbsBound C coefficients →
  Abs.absℝ x ≤ℝ Real.ιℚ (fst q) →
  ∀ n →
  Abs.absℝ (powerSeriesTerms coefficients x n) ≤ℝ
  coefficientGeometricMajorant C q n
powerSeriesTermAbsBound C q coefficients x bounded absx≤q =
  powerSeriesTermAbsBoundByCoefficientMajorant
    coefficients (constantCoefficientMajorant C)
    x (Real.ιℚ (fst q))
    (coefficientAbsBoundIsMajorized C coefficients bounded)
    absx≤q


coefficientGeometricMajorantIsCauchy : ∀ C q →
  fst q ℚ.< 1 →
  IsCauchySeries (coefficientGeometricMajorant C q)
coefficientGeometricMajorantIsCauchy C q q<1 =
  scaleSeriesIsCauchy
    (Real.ιℚ (fst C))
    (geometricTerms (Real.ιℚ (fst q)))
    (positiveRationalGeometricSeriesIsCauchy q q<1)


coefficientGeometricMajorantSummable : ∀ C q →
  fst q ℚ.< 1 →
  Summable (coefficientGeometricMajorant C q)
coefficientGeometricMajorantSummable C q q<1 =
  scaleSummable
    (Real.ιℚ (fst C))
    (geometricTerms (Real.ιℚ (fst q)))
    (rationalGeometricSeriesSummable
      (fst q) (ℚ.<Weaken≤ 0 (fst q) (snd q)) q<1)


powerSeriesIsAbsolutelyCauchyByMajorant : ∀ C q coefficients x →
  CoefficientAbsBound C coefficients →
  Abs.absℝ x ≤ℝ Real.ιℚ (fst q) →
  fst q ℚ.< 1 →
  IsAbsolutelyCauchySeries (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelyCauchyByMajorant
  C q coefficients x bounded absx≤q q<1 =
  powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
    coefficients (constantCoefficientMajorant C)
    x (Real.ιℚ (fst q))
    (coefficientAbsBoundIsMajorized C coefficients bounded)
    absx≤q
    (subst IsCauchySeries
      (sym (coefficientGeometricMajorantPath C q))
      (coefficientGeometricMajorantIsCauchy C q q<1))


powerSeriesIsAbsolutelyCauchy : ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  RationalContractionBound x →
  IsAbsolutelyCauchySeries (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelyCauchy
  C coefficients x bounded (q , absx<q , q<1) =
  powerSeriesIsAbsolutelyCauchyByMajorant C q coefficients x bounded
    (<ℝ-weaken (Abs.absℝ x) (Real.ιℚ (fst q)) absx<q)
    q<1


powerSeriesIsCauchy : ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  RationalContractionBound x →
  IsCauchySeries (powerSeriesTerms coefficients x)
powerSeriesIsCauchy C coefficients x bounded contraction =
  absoluteCauchySeriesIsCauchy (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchy
      C coefficients x bounded contraction)


powerSeriesIsSummable : ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  RationalContractionBound x →
  PowerSeriesSummableAt coefficients x
powerSeriesIsSummable C coefficients x bounded contraction =
  absoluteCauchySeriesIsSummable (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchy
      C coefficients x bounded contraction)


powerSeriesIsAbsolutelySummable : ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  RationalContractionBound x →
  AbsolutelySummable (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelySummable C coefficients x bounded contraction =
  absoluteCauchySeriesIsAbsolutelySummable
    (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchy
      C coefficients x bounded contraction)


-- As for geometric series, the rational contraction witness can remain
-- truncated when the result is a proposition.  These variants expose the
-- sharp open-unit-ball hypothesis without asking callers to choose a
-- rational radius.

powerSeriesIsAbsolutelyCauchyOfAbs<1 : ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  Abs.absℝ x <ℝ oneℝ →
  IsAbsolutelyCauchySeries (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelyCauchyOfAbs<1
  C coefficients x bounded absx<1 =
  PT.rec
    (isPropIsCauchySeries
      (λ n → Abs.absℝ (powerSeriesTerms coefficients x n)))
    (powerSeriesIsAbsolutelyCauchy C coefficients x bounded)
    (abs<1→mereRationalContractionBound x absx<1)


powerSeriesIsCauchyOfAbs<1 : ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  Abs.absℝ x <ℝ oneℝ →
  IsCauchySeries (powerSeriesTerms coefficients x)
powerSeriesIsCauchyOfAbs<1 C coefficients x bounded absx<1 =
  absoluteCauchySeriesIsCauchy (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchyOfAbs<1
      C coefficients x bounded absx<1)


powerSeriesIsAbsolutelySummableOfAbs<1 : ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  Abs.absℝ x <ℝ oneℝ →
  AbsolutelySummable (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelySummableOfAbs<1
  C coefficients x bounded absx<1 =
  absoluteCauchySeriesIsAbsolutelySummable
    (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchyOfAbs<1
      C coefficients x bounded absx<1)


powerSeriesIsSummableOfAbs<1 : ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  Abs.absℝ x <ℝ oneℝ →
  PowerSeriesSummableAt coefficients x
powerSeriesIsSummableOfAbs<1 C coefficients x bounded absx<1 =
  absoluteCauchySeriesIsSummable (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchyOfAbs<1
      C coefficients x bounded absx<1)

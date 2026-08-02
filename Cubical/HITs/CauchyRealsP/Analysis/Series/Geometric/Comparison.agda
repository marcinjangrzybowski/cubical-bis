module Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Rational
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Convergence

RationalContractionBound : ℝ → Type
RationalContractionBound x =
  Σ[ q ∈ ℚ₊ ]
    ((absℝ x <ℝ rat (fst q))
    × (fst q ℚ.< 1))

rationalContractionBoundWithin :
  ∀ x radius →
  absℝ x ≤ℝ radius →
  RationalContractionBound radius →
  RationalContractionBound x
rationalContractionBoundWithin
  x radius absx≤radius
  (q , radius<q , q<1) =
    q
    , ≤<ℝ-trans
        (absℝ x) (absℝ radius)
        (rat (fst q))
        (≤ℝ-trans
          (absℝ x) radius
          (absℝ radius)
          absx≤radius
          (leAbs radius))
        radius<q
    , q<1

rationalContractionBound→abs<1 :
  ∀ x →
  RationalContractionBound x →
  absℝ x <ℝ 1
rationalContractionBound→abs<1
  x (q , absx<q , q<1) =
    <ℝ-trans
      (absℝ x) (rat (fst q)) 1
      absx<q
      (<ℚ→<ℝ (fst q) 1 q<1)

rationalContractionBound→x<1 :
  ∀ x →
  RationalContractionBound x →
  x <ℝ 1
rationalContractionBound→x<1 x bound =
  ≤<ℝ-trans
    x (absℝ x) 1
    (leAbs x)
    (rationalContractionBound→abs<1
      x bound)

geometricSeriesIsAbsolutelyCauchyByRationalBound :
  ∀ x →
  (bound : RationalContractionBound x) →
  IsCauchySeries
    (geometricTerms (rat (fst (fst bound)))) →
  IsAbsolutelyCauchySeries (geometricTerms x)
geometricSeriesIsAbsolutelyCauchyByRationalBound
  x (q , absx<q , q<1)
  rational-series-cauchy =
    dominatedCauchySeriesIsCauchy
      (absℝ ∘ geometricTerms x)
      (geometricTerms (rat (fst q)))
      dominates
      rational-series-cauchy
  where
  absx≤q : absℝ x ≤ℝ rat (fst q)
  absx≤q =
    <ℝ-weaken
      (absℝ x) (rat (fst q)) absx<q

  dominates : ∀ n →
    absℝ (absℝ (x ^ⁿ n)) ≤ℝ
    rat (fst q) ^ⁿ n
  dominates n =
    subst
      (_≤ℝ rat (fst q) ^ⁿ n)
      (sym
        (absIdem (x ^ⁿ n)
        ∙ absPow n x))
      (powMonoℝ n
        (absNonnegative x)
        absx≤q)

geometricSeriesIsCauchyByRationalBound :
  ∀ x →
  (bound : RationalContractionBound x) →
  IsCauchySeries
    (geometricTerms (rat (fst (fst bound)))) →
  IsCauchySeries (geometricTerms x)
geometricSeriesIsCauchyByRationalBound
  x bound rational-series-cauchy =
    absoluteCauchySeriesIsCauchy
      (geometricTerms x)
      (geometricSeriesIsAbsolutelyCauchyByRationalBound
        x bound rational-series-cauchy)

geometricSeriesIsSummableByRationalBound :
  ∀ x →
  (bound : RationalContractionBound x) →
  IsCauchySeries
    (geometricTerms (rat (fst (fst bound)))) →
  Summable (geometricTerms x)
geometricSeriesIsSummableByRationalBound
  x bound rational-series-cauchy =
    absoluteCauchySeriesIsSummable
      (geometricTerms x)
      (geometricSeriesIsAbsolutelyCauchyByRationalBound
        x bound rational-series-cauchy)

geometricSeriesHasSumByRationalBound :
  ∀ x →
  (bound : RationalContractionBound x) →
  IsCauchySeries
    (geometricTerms (rat (fst (fst bound)))) →
  HasSum
    (geometricTerms x)
    (positiveReciprocal
      (1 - x)
      (positiveSub x 1
        (rationalContractionBound→x<1 x bound)))
geometricSeriesHasSumByRationalBound
  x bound rational-series-cauchy =
    geometricSeriesHasSum
      x x<1
      (absLimitZeroReflects
        (geometricTerms x)
        (summableTermsTendToZero
          (absℝ ∘ geometricTerms x)
          (cauchySeriesIsSummable
            (absℝ ∘ geometricTerms x)
            (geometricSeriesIsAbsolutelyCauchyByRationalBound
              x bound rational-series-cauchy))))
  where
  x<1 : x <ℝ 1
  x<1 =
    rationalContractionBound→x<1 x bound

positiveRationalGeometricSeriesIsCauchy :
  ∀ q →
  fst q ℚ.< 1 →
  IsCauchySeries
    (geometricTerms (rat (fst q)))
positiveRationalGeometricSeriesIsCauchy
  q q<1 =
    rationalGeometricSeriesIsCauchy
      (fst q)
      (ℚ.<Weaken≤ 0 (fst q) (snd q))
      q<1

geometricSeriesIsAbsolutelyCauchyByRationalContraction :
  ∀ x →
  RationalContractionBound x →
  IsAbsolutelyCauchySeries (geometricTerms x)
geometricSeriesIsAbsolutelyCauchyByRationalContraction
  x bound =
    geometricSeriesIsAbsolutelyCauchyByRationalBound
      x bound
      (positiveRationalGeometricSeriesIsCauchy
        (fst bound)
        (snd (snd bound)))

geometricSeriesIsCauchyByRationalContraction :
  ∀ x →
  RationalContractionBound x →
  IsCauchySeries (geometricTerms x)
geometricSeriesIsCauchyByRationalContraction
  x bound =
    geometricSeriesIsCauchyByRationalBound
      x bound
      (positiveRationalGeometricSeriesIsCauchy
        (fst bound)
        (snd (snd bound)))

geometricSeriesIsSummableByRationalContraction :
  ∀ x →
  RationalContractionBound x →
  Summable (geometricTerms x)
geometricSeriesIsSummableByRationalContraction
  x bound =
    geometricSeriesIsSummableByRationalBound
      x bound
      (positiveRationalGeometricSeriesIsCauchy
        (fst bound)
        (snd (snd bound)))

geometricSeriesHasSumByRationalContraction :
  ∀ x →
  (bound : RationalContractionBound x) →
  HasSum
    (geometricTerms x)
    (positiveReciprocal
      (1 - x)
      (positiveSub x 1
        (rationalContractionBound→x<1
          x bound)))
geometricSeriesHasSumByRationalContraction
  x bound =
    geometricSeriesHasSumByRationalBound
      x bound
      (positiveRationalGeometricSeriesIsCauchy
        (fst bound)
        (snd (snd bound)))

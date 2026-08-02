module Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Base

GeometricPowersTendToZero : ℝ → Type
GeometricPowersTendToZero x =
  isLimitSeq (geometricTerms x) 0

geometricAbsoluteTermsPath : ∀ x →
  (absℝ ∘ geometricTerms x) ≡
  geometricTerms (absℝ x)
geometricAbsoluteTermsPath x =
  funExt λ n →
    absPow n x

geometricSeriesIsAbsolutelyCauchy :
  ∀ x →
  IsCauchySeries (geometricTerms (absℝ x)) →
  IsAbsolutelyCauchySeries (geometricTerms x)
geometricSeriesIsAbsolutelyCauchy
  x absolute-powers-cauchy =
    subst IsCauchySeries
      (sym (geometricAbsoluteTermsPath x))
      absolute-powers-cauchy

geometricSeriesIsCauchy :
  ∀ x →
  IsCauchySeries (geometricTerms (absℝ x)) →
  IsCauchySeries (geometricTerms x)
geometricSeriesIsCauchy x absolute-powers-cauchy =
  absoluteCauchySeriesIsCauchy
    (geometricTerms x)
    (geometricSeriesIsAbsolutelyCauchy
      x absolute-powers-cauchy)

geometricSeriesIsSummable :
  ∀ x →
  IsCauchySeries (geometricTerms (absℝ x)) →
  Summable (geometricTerms x)
geometricSeriesIsSummable x absolute-powers-cauchy =
  absoluteCauchySeriesIsSummable
    (geometricTerms x)
    (geometricSeriesIsAbsolutelyCauchy
      x absolute-powers-cauchy)

geometricPowersTendToZero :
  ∀ x →
  IsCauchySeries (geometricTerms (absℝ x)) →
  GeometricPowersTendToZero x
geometricPowersTendToZero x absolute-powers-cauchy =
  absLimitZeroReflects
    (geometricTerms x)
    (subst
      (λ terms → isLimitSeq terms 0)
      (sym (geometricAbsoluteTermsPath x))
      (summableTermsTendToZero
        (geometricTerms (absℝ x))
        (cauchySeriesIsSummable
          (geometricTerms (absℝ x))
          absolute-powers-cauchy)))

geometricSeriesHasSum :
  ∀ x →
  (x<1 : x <ℝ 1) →
  GeometricPowersTendToZero x →
  HasSum
    (geometricTerms x)
    (positiveReciprocal (1 - x)
      (positiveSub x 1 x<1))
geometricSeriesHasSum x x<1 powers-limit =
  eventuallyEqualSeqPresIsLimitSeq
    candidate
    (partialSum (geometricTerms x))
    reciprocal
    ( 0
    , λ n _ →
        sym
          (geometricPartialSumByReciprocal
            x n positive-denominator)
    )
    candidate-limit
  where
  positive-denominator : 0 <ℝ 1 - x
  positive-denominator =
    positiveSub x 1 x<1

  reciprocal : ℝ
  reciprocal =
    positiveReciprocal
      (1 - x) positive-denominator

  one-minus-powers : RealSequence
  one-minus-powers n =
    1 - x ^ⁿ n

  one-minus-powers-limit :
    isLimitSeq one-minus-powers 1
  one-minus-powers-limit =
    subst
      (isLimitSeq one-minus-powers)
      (subZeroR 1)
      (subPresIsLimitSeq
        (λ _ → 1)
        (geometricTerms x)
        1 0
        (constantIsLimitSeq 1)
        powers-limit)

  candidate : RealSequence
  candidate n =
    reciprocal · one-minus-powers n

  candidate-limit :
    isLimitSeq candidate reciprocal
  candidate-limit =
    subst
      (isLimitSeq candidate)
      (mulIdR reciprocal)
      (mulPresIsLimitSeq
        (λ _ → reciprocal)
        one-minus-powers
        reciprocal 1
        (constantIsLimitSeq reciprocal)
        one-minus-powers-limit)

geometricSeriesSummable :
  ∀ x →
  x <ℝ 1 →
  GeometricPowersTendToZero x →
  Summable (geometricTerms x)
geometricSeriesSummable x x<1 powers-limit =
  positiveReciprocal
    (1 - x) (positiveSub x 1 x<1)
  , geometricSeriesHasSum x x<1 powers-limit

seriesSum-geometric :
  ∀ x →
  (x<1 : x <ℝ 1) →
  (powers-limit : GeometricPowersTendToZero x) →
  (summable : Summable (geometricTerms x)) →
  seriesSum (geometricTerms x) summable ≡
  positiveReciprocal
    (1 - x) (positiveSub x 1 x<1)
seriesSum-geometric x x<1 powers-limit summable =
  seriesSumIndependent
    (geometricTerms x)
    summable
    (geometricSeriesSummable
      x x<1 powers-limit)

absoluteCauchyGeometricSeriesHasSum :
  ∀ x →
  (x<1 : x <ℝ 1) →
  IsCauchySeries (geometricTerms (absℝ x)) →
  HasSum
    (geometricTerms x)
    (positiveReciprocal (1 - x)
      (positiveSub x 1 x<1))
absoluteCauchyGeometricSeriesHasSum
  x x<1 absolute-powers-cauchy =
    geometricSeriesHasSum
      x x<1
      (geometricPowersTendToZero
        x absolute-powers-cauchy)

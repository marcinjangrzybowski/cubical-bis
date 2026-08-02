module Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.FiniteSum
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations

absolutePartialSum : RealSequence → RealSequence
absolutePartialSum terms =
  partialSum (absℝ ∘ terms)

IsAbsolutelyCauchySeries : RealSequence → Type
IsAbsolutelyCauchySeries terms =
  IsCauchySeries (absℝ ∘ terms)

AbsolutelySummable : RealSequence → Type
AbsolutelySummable terms =
  Summable (absℝ ∘ terms)

dominatedCauchySeriesIsCauchy :
  (terms bound : RealSequence) →
  (∀ n → absℝ (terms n) ≤ℝ bound n) →
  IsCauchySeries bound →
  IsCauchySeries terms
dominatedCauchySeriesIsCauchy
  terms bound dominates bound-cauchy .fst =
    fst bound-cauchy
dominatedCauchySeriesIsCauchy
  terms bound dominates bound-cauchy
  .snd ε m n modulus≤m modulus≤n =
    absDifference<→closeness
      (partialSum terms m)
      (partialSum terms n)
      ε
      (≤<ℝ-trans
        (absℝ
          (partialSum terms m
            - partialSum terms n))
        (absℝ
          (partialSum bound m
            - partialSum bound n))
        (rat (fst ε))
        (partialSumDistanceBoundBy
          terms bound dominates m n)
        (closeness→absDifference<
          (partialSum bound m)
          (partialSum bound n)
          ε
          (snd bound-cauchy ε m n
            modulus≤m modulus≤n)))

dominatedCauchySeriesIsSummable :
  (terms bound : RealSequence) →
  (∀ n → absℝ (terms n) ≤ℝ bound n) →
  IsCauchySeries bound →
  Summable terms
dominatedCauchySeriesIsSummable
  terms bound dominates bound-cauchy =
    cauchySeriesIsSummable terms
      (dominatedCauchySeriesIsCauchy
        terms bound dominates bound-cauchy)

absoluteCauchySeriesIsCauchy :
  (terms : RealSequence) →
  IsAbsolutelyCauchySeries terms →
  IsCauchySeries terms
absoluteCauchySeriesIsCauchy terms =
  dominatedCauchySeriesIsCauchy
    terms (absℝ ∘ terms)
    (λ n → ≤ℝ-refl (absℝ (terms n)))

absoluteCauchySeriesIsSummable :
  (terms : RealSequence) →
  IsAbsolutelyCauchySeries terms →
  Summable terms
absoluteCauchySeriesIsSummable terms absolute =
  cauchySeriesIsSummable terms
    (absoluteCauchySeriesIsCauchy terms absolute)

absoluteCauchySeriesIsAbsolutelySummable :
  (terms : RealSequence) →
  IsAbsolutelyCauchySeries terms →
  AbsolutelySummable terms
absoluteCauchySeriesIsAbsolutelySummable terms =
  cauchySeriesIsSummable (absℝ ∘ terms)

rationalScaleSeriesIsAbsolutelyCauchy :
  ∀ q terms →
  IsAbsolutelyCauchySeries terms →
  IsAbsolutelyCauchySeries
    (scaleSeries (rat q) terms)
rationalScaleSeriesIsAbsolutelyCauchy
  q terms absolute =
    subst
      IsCauchySeries
      (sym absolute-scaled-path)
      (rationalScaleSeriesIsCauchy
        (abs q)
        (absℝ ∘ terms)
        absolute)
  where
  absolute-scaled-path :
    (absℝ
      ∘ scaleSeries (rat q) terms)
      ≡
    scaleSeries
      (rat (abs q))
      (absℝ ∘ terms)
  absolute-scaled-path =
    funExt
      (λ n →
        absMul (rat q) (terms n)
        ∙ cong
            (_· absℝ (terms n))
            (abs-rat q))

absoluteCauchySeriesSumAbsBound :
  (terms : RealSequence) →
  (absolute : IsAbsolutelyCauchySeries terms) →
  absℝ
    (seriesSum terms
      (absoluteCauchySeriesIsSummable terms absolute))
    ≤ℝ
  seriesSum (absℝ ∘ terms)
    (absoluteCauchySeriesIsAbsolutelySummable
      terms absolute)
absoluteCauchySeriesSumAbsBound terms absolute =
  seriesSumAbsBound
    terms
    (absoluteCauchySeriesIsSummable terms absolute)
    (absoluteCauchySeriesIsAbsolutelySummable
      terms absolute)

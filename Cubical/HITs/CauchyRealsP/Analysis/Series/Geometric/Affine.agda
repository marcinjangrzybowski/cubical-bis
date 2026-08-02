module Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Affine where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison

geometricReciprocal : ∀ x →
  RationalContractionBound x →
  ℝ
geometricReciprocal x contraction =
  positiveReciprocal
    (1 - x)
    (positiveSub x 1
      (rationalContractionBound→x<1
        x contraction))

scaledGeometricTerms : ℝ → ℝ → RealSequence
scaledGeometricTerms coefficient ratio =
  scaleSeries coefficient (geometricTerms ratio)

scaledGeometricSeriesHasSum : ∀ coefficient ratio →
  (contraction : RationalContractionBound ratio) →
  HasSum
    (scaledGeometricTerms coefficient ratio)
    (coefficient
      · geometricReciprocal ratio contraction)
scaledGeometricSeriesHasSum
  coefficient ratio contraction =
    scaleHasSum
      coefficient
      (geometricTerms ratio)
      (geometricReciprocal ratio contraction)
      (geometricSeriesHasSumByRationalContraction
        ratio contraction)

scaledGeometricSeriesSummable : ∀ coefficient ratio →
  RationalContractionBound ratio →
  Summable (scaledGeometricTerms coefficient ratio)
scaledGeometricSeriesSummable
  coefficient ratio contraction =
    coefficient
      · geometricReciprocal ratio contraction
    , scaledGeometricSeriesHasSum
        coefficient ratio contraction

seriesSum-scaledGeometric : ∀ coefficient ratio →
  (contraction : RationalContractionBound ratio) →
  (summable :
    Summable (scaledGeometricTerms coefficient ratio)) →
  seriesSum
      (scaledGeometricTerms coefficient ratio)
      summable
    ≡
  coefficient
    · geometricReciprocal ratio contraction
seriesSum-scaledGeometric
  coefficient ratio contraction summable =
    seriesSumIndependent
      (scaledGeometricTerms coefficient ratio)
      summable
      (scaledGeometricSeriesSummable
        coefficient ratio contraction)

shiftedGeometricTerms : ℕ → ℝ → RealSequence
shiftedGeometricTerms start ratio =
  dropSeries start (geometricTerms ratio)

shiftedGeometricTerms-scale : ∀ start ratio →
  shiftedGeometricTerms start ratio
    ≡
  scaledGeometricTerms (ratio ^ⁿ start) ratio
shiftedGeometricTerms-scale start ratio =
  funExt λ n →
    cong (ratio ^ⁿ_)
      (ℕ.+-comm n start)
    ∙ sym
        (ℝExponentiation.·-of-^-is-^-of-+
          ratio start n)

shiftedGeometricSeriesHasSum : ∀ start ratio →
  (contraction : RationalContractionBound ratio) →
  HasSum
    (shiftedGeometricTerms start ratio)
    (ratio ^ⁿ start
      · geometricReciprocal ratio contraction)
shiftedGeometricSeriesHasSum
  start ratio contraction =
    subst
      (λ terms →
        HasSum terms
          (ratio ^ⁿ start
            · geometricReciprocal
                ratio contraction))
      (sym (shiftedGeometricTerms-scale start ratio))
      (scaledGeometricSeriesHasSum
        (ratio ^ⁿ start) ratio contraction)

shiftedGeometricSeriesSummable : ∀ start ratio →
  RationalContractionBound ratio →
  Summable (shiftedGeometricTerms start ratio)
shiftedGeometricSeriesSummable
  start ratio contraction =
    ratio ^ⁿ start
      · geometricReciprocal ratio contraction
    , shiftedGeometricSeriesHasSum
        start ratio contraction

seriesSum-shiftedGeometric : ∀ start ratio →
  (contraction : RationalContractionBound ratio) →
  (summable :
    Summable (shiftedGeometricTerms start ratio)) →
  seriesSum
      (shiftedGeometricTerms start ratio)
      summable
    ≡
  ratio ^ⁿ start
    · geometricReciprocal ratio contraction
seriesSum-shiftedGeometric
  start ratio contraction summable =
    seriesSumIndependent
      (shiftedGeometricTerms start ratio)
      summable
      (shiftedGeometricSeriesSummable
        start ratio contraction)

EventuallyScaledGeometricFrom :
  ℕ → ℝ → ℝ → RealSequence → Type
EventuallyScaledGeometricFrom
  start coefficient ratio terms =
    dropSeries start terms
      ≡
    scaledGeometricTerms coefficient ratio

eventuallyScaledGeometricHasSum :
  ∀ start coefficient ratio terms →
  EventuallyScaledGeometricFrom
    start coefficient ratio terms →
  (contraction : RationalContractionBound ratio) →
  HasSum terms
    ( partialSum terms start
    + coefficient
      · geometricReciprocal ratio contraction
    )
eventuallyScaledGeometricHasSum
  start coefficient ratio terms tail-path contraction =
    dropSeriesReflectsHasSum
      start terms
      (coefficient
        · geometricReciprocal ratio contraction)
      tail-has-sum
  where
  tail-has-sum :
    HasSum
      (dropSeries start terms)
      (coefficient
        · geometricReciprocal ratio contraction)
  tail-has-sum =
    subst
      (λ sequence →
        HasSum sequence
          (coefficient
            · geometricReciprocal
                ratio contraction))
      (sym tail-path)
      (scaledGeometricSeriesHasSum
        coefficient ratio contraction)

eventuallyScaledGeometricSummable :
  ∀ start coefficient ratio terms →
  EventuallyScaledGeometricFrom
    start coefficient ratio terms →
  RationalContractionBound ratio →
  Summable terms
eventuallyScaledGeometricSummable
  start coefficient ratio terms tail-path contraction =
    partialSum terms start
      + coefficient
        · geometricReciprocal ratio contraction
    , eventuallyScaledGeometricHasSum
        start coefficient ratio terms
        tail-path contraction

seriesSum-eventuallyScaledGeometric :
  ∀ start coefficient ratio terms →
  (tail-path :
    EventuallyScaledGeometricFrom
      start coefficient ratio terms) →
  (contraction : RationalContractionBound ratio) →
  (summable : Summable terms) →
  seriesSum terms summable
    ≡
  partialSum terms start
    + coefficient
      · geometricReciprocal ratio contraction
seriesSum-eventuallyScaledGeometric
  start coefficient ratio terms
  tail-path contraction summable =
    seriesSumIndependent
      terms summable
      (eventuallyScaledGeometricSummable
        start coefficient ratio terms
        tail-path contraction)

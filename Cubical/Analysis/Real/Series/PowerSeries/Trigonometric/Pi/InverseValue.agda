module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseValue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Existence
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Continuity
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value

opaque
  sinℝ-restricted-isEquiv : isEquiv (restrictedSine halfPiℝ)
  sinℝ-restricted-isEquiv =
    restrictedSine-isEquiv halfPiℝ halfPiℝ-quarterTurn halfPiℝ-characterization

sinℝ-restrictedEquiv : SineQuarterInterval halfPiℝ ≃ SineUnitInterval
sinℝ-restrictedEquiv = restrictedSine halfPiℝ , sinℝ-restricted-isEquiv

cosℝ-restrictedEquiv : CosineHalfInterval halfPiℝ ≃ SineUnitInterval
cosℝ-restrictedEquiv =
  restrictedCosineEquivFromSine halfPiℝ halfPiℝ-quarterTurn sinℝ-restricted-isEquiv

-- The subtype domains and codomains record all endpoint/range restrictions.
-- No IVT, approximation, modulus, or equivalence argument is required.
arcSinℝ : SineUnitInterval → SineQuarterInterval halfPiℝ
arcSinℝ = restrictedArcSin halfPiℝ sinℝ-restricted-isEquiv

arcCosℝ : SineUnitInterval → CosineHalfInterval halfPiℝ
arcCosℝ = restrictedArcCos halfPiℝ sinℝ-restricted-isEquiv

private
  opaque
    arcSinDefinition : ∀ (value : SineUnitInterval) →
      arcSinℝ value ≡ restrictedArcSin halfPiℝ sinℝ-restricted-isEquiv value
    arcSinDefinition value = refl

    arcCosDefinition : ∀ (value : SineUnitInterval) →
      arcCosℝ value ≡ restrictedArcCos halfPiℝ sinℝ-restricted-isEquiv value
    arcCosDefinition value = refl

opaque
  restrictedSine-arcSinℝ : ∀ (value : SineUnitInterval) → restrictedSine halfPiℝ (arcSinℝ value) ≡ value
  restrictedSine-arcSinℝ value =
    cong (restrictedSine halfPiℝ) (arcSinDefinition value)
    ∙ restrictedSine-arcSin halfPiℝ sinℝ-restricted-isEquiv value

  arcSinℝ-restrictedSine : ∀ (point : SineQuarterInterval halfPiℝ) → arcSinℝ (restrictedSine halfPiℝ point) ≡ point
  arcSinℝ-restrictedSine point =
    arcSinDefinition (restrictedSine halfPiℝ point)
    ∙ restrictedArcSin-sine halfPiℝ sinℝ-restricted-isEquiv point

  restrictedCosine-arcCosℝ : ∀ (value : SineUnitInterval) → restrictedCosine halfPiℝ (arcCosℝ value) ≡ value
  restrictedCosine-arcCosℝ value =
    cong (restrictedCosine halfPiℝ) (arcCosDefinition value)
    ∙ restrictedCosine-arcCos halfPiℝ halfPiℝ-quarterTurn sinℝ-restricted-isEquiv value

  arcCosℝ-restrictedCosine : ∀ (point : CosineHalfInterval halfPiℝ) → arcCosℝ (restrictedCosine halfPiℝ point) ≡ point
  arcCosℝ-restrictedCosine point =
    arcCosDefinition (restrictedCosine halfPiℝ point)
    ∙ restrictedArcCos-cosine halfPiℝ halfPiℝ-quarterTurn sinℝ-restricted-isEquiv point

  sinℝ-arcSinℝ : ∀ (value : SineUnitInterval) → sinℝ (fst (arcSinℝ value)) ≡ fst value
  sinℝ-arcSinℝ value =
    sym (restrictedSine-value halfPiℝ (arcSinℝ value))
    ∙ cong fst (restrictedSine-arcSinℝ value)

  cosℝ-arcCosℝ : ∀ (value : SineUnitInterval) → cosℝ (fst (arcCosℝ value)) ≡ fst value
  cosℝ-arcCosℝ value =
    sym (restrictedCosine-value halfPiℝ (arcCosℝ value))
    ∙ cong fst (restrictedCosine-arcCosℝ value)

  arcSinℝ-unique : ∀ (value : SineUnitInterval) (point : SineQuarterInterval halfPiℝ) → sinℝ (fst point) ≡ fst value → arcSinℝ value ≡ point
  arcSinℝ-unique = restrictedArcSin-unique halfPiℝ sinℝ-restricted-isEquiv

  arcCosℝ-unique : ∀ (value : SineUnitInterval) (point : CosineHalfInterval halfPiℝ) → cosℝ (fst point) ≡ fst value → arcCosℝ value ≡ point
  arcCosℝ-unique = restrictedArcCos-unique halfPiℝ halfPiℝ-quarterTurn sinℝ-restricted-isEquiv

  arcCosℝ-asArcSin : ∀ (value : SineUnitInterval) → fst (arcCosℝ value) ≡ halfPiℝ - fst (arcSinℝ value)
  arcCosℝ-asArcSin = restrictedArcCos-value halfPiℝ sinℝ-restricted-isEquiv

arcSinℝ-isContinuous : isContinuous
  (ClosedIntervalPremetricSpace (- 1ℝ) 1ℝ .snd) arcSinℝ
  (ClosedIntervalPremetricSpace (- halfPiℝ) halfPiℝ .snd)
arcSinℝ-isContinuous = restrictedArcSinIsContinuous halfPiℝ sinℝ-restricted-isEquiv
  (characterizedQuarterTurn-sineClosenessReflectionModulus
    halfPiℝ halfPiℝ-quarterTurn halfPiℝ-characterization)

arcCosℝ-isContinuous : isContinuous
  (ClosedIntervalPremetricSpace (- 1ℝ) 1ℝ .snd) arcCosℝ
  (ClosedIntervalPremetricSpace 0ℝ piℝ .snd)
arcCosℝ-isContinuous = restrictedArcCosIsContinuous halfPiℝ sinℝ-restricted-isEquiv
  (characterizedQuarterTurn-sineClosenessReflectionModulus
    halfPiℝ halfPiℝ-quarterTurn halfPiℝ-characterization)

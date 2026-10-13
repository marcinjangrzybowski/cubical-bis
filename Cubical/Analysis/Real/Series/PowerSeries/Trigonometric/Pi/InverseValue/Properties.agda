module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseValue.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Relation.Premetric.Mappings using (IsNonExpanding)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/4₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Values
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Endpoints
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Monotonicity
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.StrictMonotonicity
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Quantitative
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseValue

private
  opaque
    halfPi-nonnegative : 0ℝ ≤ℝ halfPiℝ
    halfPi-nonnegative = <ℝ-weaken 0ℝ halfPiℝ halfPiℝ-positive

opaque
  arcSinℝ-zero : fst (arcSinℝ sineUnitZero) ≡ 0ℝ
  arcSinℝ-zero = restrictedArcSin-zero halfPiℝ halfPi-nonnegative sinℝ-restricted-isEquiv

  arcCosℝ-zero : fst (arcCosℝ sineUnitZero) ≡ halfPiℝ
  arcCosℝ-zero = restrictedArcCos-zero halfPiℝ halfPi-nonnegative sinℝ-restricted-isEquiv

  arcSinℝ-left : fst (arcSinℝ sineUnitLeft) ≡ - halfPiℝ
  arcSinℝ-left = restrictedArcSin-left halfPiℝ halfPiℝ-quarterTurn halfPi-nonnegative sinℝ-restricted-isEquiv

  arcSinℝ-right : fst (arcSinℝ sineUnitRight) ≡ halfPiℝ
  arcSinℝ-right = restrictedArcSin-right halfPiℝ halfPiℝ-quarterTurn halfPi-nonnegative sinℝ-restricted-isEquiv

  arcCosℝ-left : fst (arcCosℝ sineUnitLeft) ≡ piℝ
  arcCosℝ-left = restrictedArcCos-left halfPiℝ halfPiℝ-quarterTurn halfPi-nonnegative sinℝ-restricted-isEquiv

  arcCosℝ-right : fst (arcCosℝ sineUnitRight) ≡ 0ℝ
  arcCosℝ-right = restrictedArcCos-right halfPiℝ halfPiℝ-quarterTurn halfPi-nonnegative sinℝ-restricted-isEquiv

  arcSinℝ-odd : ∀ (value : SineUnitInterval) → fst (arcSinℝ (sineUnitNegate value)) ≡ - fst (arcSinℝ value)
  arcSinℝ-odd = restrictedArcSin-odd halfPiℝ sinℝ-restricted-isEquiv

  arcCosℝ-negate : ∀ (value : SineUnitInterval) →
    fst (arcCosℝ (sineUnitNegate value)) ≡ piℝ - fst (arcCosℝ value)
  arcCosℝ-negate = restrictedArcCos-negate halfPiℝ sinℝ-restricted-isEquiv

  arcSinℝ-increasing : ∀ (left right : SineUnitInterval) → fst left ≤ℝ fst right →
    fst (arcSinℝ left) ≤ℝ fst (arcSinℝ right)
  arcSinℝ-increasing = restrictedArcSin-increasing halfPiℝ
    halfPiℝ-quarterTurn halfPiℝ-characterization sinℝ-restricted-isEquiv

  arcCosℝ-decreasing : ∀ (left right : SineUnitInterval) → fst left ≤ℝ fst right →
    fst (arcCosℝ right) ≤ℝ fst (arcCosℝ left)
  arcCosℝ-decreasing = restrictedArcCos-decreasing halfPiℝ
    halfPiℝ-quarterTurn halfPiℝ-characterization sinℝ-restricted-isEquiv

  arcSinℝ-strictlyIncreasing : ∀ (left right : SineUnitInterval) → fst left <ℝ fst right →
    fst (arcSinℝ left) <ℝ fst (arcSinℝ right)
  arcSinℝ-strictlyIncreasing = restrictedArcSin-strictlyIncreasing halfPiℝ
    halfPiℝ-quarterTurn halfPiℝ-characterization sinℝ-restricted-isEquiv

  arcCosℝ-strictlyDecreasing : ∀ (left right : SineUnitInterval) → fst left <ℝ fst right →
    fst (arcCosℝ right) <ℝ fst (arcCosℝ left)
  arcCosℝ-strictlyDecreasing = restrictedArcCos-strictlyDecreasing halfPiℝ
    halfPiℝ-quarterTurn halfPiℝ-characterization sinℝ-restricted-isEquiv

-- A single rational formula controls both inverse functions, endpoints included.
inverseTrigRadius : ℚ₊ → ℚ₊
inverseTrigRadius ε = sineSeparationOutput (ε /4₊)

opaque
  arcSinℝ-pres∼ : ∀ (ε : ℚ₊) (left right : SineUnitInterval) →
    fst left ∼[ inverseTrigRadius ε ] fst right →
    fst (arcSinℝ left) ∼[ ε ] fst (arcSinℝ right)
  arcSinℝ-pres∼ ε left right close =
    snd (characterizedQuarterTurn-chosenSineClosenessReflectionModulus
      halfPiℝ halfPiℝ-quarterTurn halfPiℝ-characterization ε)
      (arcSinℝ left) (arcSinℝ right)
      (subst2 (_∼[ inverseTrigRadius ε ]_)
        (sym (sinℝ-arcSinℝ left)) (sym (sinℝ-arcSinℝ right)) close)

  arcCosℝ-pres∼ : ∀ (ε : ℚ₊) (left right : SineUnitInterval) →
    fst left ∼[ inverseTrigRadius ε ] fst right →
    fst (arcCosℝ left) ∼[ ε ] fst (arcCosℝ right)
  arcCosℝ-pres∼ ε left right close =
    subst2 (_∼[ ε ]_) (sym (arcCosℝ-asArcSin left)) (sym (arcCosℝ-asArcSin right))
      (add-pres∼₂ halfPiℝ (- fst (arcSinℝ left)) (- fst (arcSinℝ right)) ε
        (IsNonExpanding.pres≈ neg-isNonExpanding
          (fst (arcSinℝ left)) (fst (arcSinℝ right)) ε
          (arcSinℝ-pres∼ ε left right close)))

module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Definition
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.QuarterTurn
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.RestrictedSine


-- Closed-domain inverses for a characterized pi.  The only additional
-- analytic input is restricted-sine intermediate value; orientation,
-- injectivity, cosine surjectivity, and inverse continuity are derived.
characterizedArcSin : (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineIntermediateValue construction →
  SineUnitInterval → SineQuarterInterval (fst construction)
characterizedArcSin construction intermediate =
  restrictedArcSin (fst construction)
    (characterizedRestrictedSine-isEquiv construction intermediate)

characterizedArcCos : (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineIntermediateValue construction →
  SineUnitInterval → CosineHalfInterval (fst construction)
characterizedArcCos construction intermediate =
  restrictedArcCos (fst construction)
    (characterizedRestrictedSine-isEquiv construction intermediate)


opaque
  characterizedRestrictedSine-arcSin : ∀ construction intermediate value →
    restrictedSine (fst construction)
      (characterizedArcSin construction intermediate value) ≡ value
  characterizedRestrictedSine-arcSin construction intermediate =
    restrictedSine-arcSin (fst construction)
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcSin-sine : ∀ construction intermediate point →
    characterizedArcSin construction intermediate
      (restrictedSine (fst construction) point) ≡ point
  characterizedArcSin-sine construction intermediate =
    restrictedArcSin-sine (fst construction)
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedRestrictedCosine-arcCos : ∀ construction intermediate value →
    restrictedCosine (fst construction)
      (characterizedArcCos construction intermediate value) ≡ value
  characterizedRestrictedCosine-arcCos construction intermediate =
    restrictedCosine-arcCos (fst construction)
      (characterizedHalfPi-quarterTurn construction)
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcCos-cosine : ∀ construction intermediate point →
    characterizedArcCos construction intermediate
      (restrictedCosine (fst construction) point) ≡ point
  characterizedArcCos-cosine construction intermediate =
    restrictedArcCos-cosine (fst construction)
      (characterizedHalfPi-quarterTurn construction)
      (characterizedRestrictedSine-isEquiv construction intermediate)

  sinℝ-characterizedArcSin : ∀ construction intermediate value →
    sinℝ (fst (characterizedArcSin construction intermediate value)) ≡ fst value
  sinℝ-characterizedArcSin construction intermediate value =
    sym (restrictedSine-value (fst construction)
      (characterizedArcSin construction intermediate value))
    ∙ cong fst (characterizedRestrictedSine-arcSin construction intermediate value)

  cosℝ-characterizedArcCos : ∀ construction intermediate value →
    cosℝ (fst (characterizedArcCos construction intermediate value)) ≡ fst value
  cosℝ-characterizedArcCos construction intermediate value =
    sym (restrictedCosine-value (fst construction)
      (characterizedArcCos construction intermediate value))
    ∙ cong fst (characterizedRestrictedCosine-arcCos construction intermediate value)


characterizedArcSinIsContinuous : ∀ construction intermediate →
  isContinuous
    (ClosedIntervalPremetricSpace (- 1ℝ) 1ℝ .snd)
    (characterizedArcSin construction intermediate)
    (ClosedIntervalPremetricSpace (- fst construction) (fst construction) .snd)
characterizedArcSinIsContinuous construction intermediate =
  restrictedArcSinIsContinuous (fst construction)
    (characterizedRestrictedSine-isEquiv construction intermediate)
    (characterizedQuarterTurn-sineClosenessReflectionModulus
      (fst construction) (characterizedHalfPi-quarterTurn construction)
      (snd construction))

characterizedArcCosIsContinuous : ∀ construction intermediate →
  isContinuous
    (ClosedIntervalPremetricSpace (- 1ℝ) 1ℝ .snd)
    (characterizedArcCos construction intermediate)
    (ClosedIntervalPremetricSpace 0ℝ (halfTurn (fst construction)) .snd)
characterizedArcCosIsContinuous construction intermediate =
  restrictedArcCosIsContinuous (fst construction)
    (characterizedRestrictedSine-isEquiv construction intermediate)
    (characterizedQuarterTurn-sineClosenessReflectionModulus
      (fst construction) (characterizedHalfPi-quarterTurn construction)
      (snd construction))

module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseProperties where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Values
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Endpoints
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Monotonicity
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.StrictMonotonicity
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Definition
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.QuarterTurn
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.RestrictedSine
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Inverse


-- These are properties of the existing conditional inverses.  Neither their
-- domains nor the analytic assumptions needed to construct them are enlarged.
module _ (construction : CharacterizedHalfPi)
  (intermediate : CharacterizedHalfPiSineIntermediateValue construction) where

  private
    nonnegative : 0ℝ ≤ℝ fst construction
    nonnegative =
      <ℝ-weaken 0ℝ (fst construction)
        (firstPositiveCosineZero-positive (snd construction))

  characterizedArcSin-zero :
    fst (characterizedArcSin construction intermediate sineUnitZero) ≡ 0ℝ
  characterizedArcSin-zero =
    restrictedArcSin-zero (fst construction) nonnegative
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcCos-zero :
    fst (characterizedArcCos construction intermediate sineUnitZero) ≡
    characterizedHalfPi construction
  characterizedArcCos-zero =
    restrictedArcCos-zero (fst construction) nonnegative
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcSin-left :
    fst (characterizedArcSin construction intermediate sineUnitLeft) ≡
    - characterizedHalfPi construction
  characterizedArcSin-left =
    restrictedArcSin-left (fst construction)
      (characterizedHalfPi-quarterTurn construction) nonnegative
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcSin-right :
    fst (characterizedArcSin construction intermediate sineUnitRight) ≡
    characterizedHalfPi construction
  characterizedArcSin-right =
    restrictedArcSin-right (fst construction)
      (characterizedHalfPi-quarterTurn construction) nonnegative
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcCos-left :
    fst (characterizedArcCos construction intermediate sineUnitLeft) ≡
    characterizedPi construction
  characterizedArcCos-left =
    restrictedArcCos-left (fst construction)
      (characterizedHalfPi-quarterTurn construction) nonnegative
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcCos-right :
    fst (characterizedArcCos construction intermediate sineUnitRight) ≡ 0ℝ
  characterizedArcCos-right =
    restrictedArcCos-right (fst construction)
      (characterizedHalfPi-quarterTurn construction) nonnegative
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcSin-odd : ∀ value →
    fst (characterizedArcSin construction intermediate (sineUnitNegate value)) ≡
    - fst (characterizedArcSin construction intermediate value)
  characterizedArcSin-odd =
    restrictedArcSin-odd (fst construction)
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcCos-negate : ∀ value →
    fst (characterizedArcCos construction intermediate (sineUnitNegate value)) ≡
    characterizedPi construction -
    fst (characterizedArcCos construction intermediate value)
  characterizedArcCos-negate =
    restrictedArcCos-negate (fst construction)
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcSin-increasing : ∀ left right → fst left ≤ℝ fst right →
    fst (characterizedArcSin construction intermediate left) ≤ℝ
    fst (characterizedArcSin construction intermediate right)
  characterizedArcSin-increasing =
    restrictedArcSin-increasing (fst construction)
      (characterizedHalfPi-quarterTurn construction) (snd construction)
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcCos-decreasing : ∀ left right → fst left ≤ℝ fst right →
    fst (characterizedArcCos construction intermediate right) ≤ℝ
    fst (characterizedArcCos construction intermediate left)
  characterizedArcCos-decreasing =
    restrictedArcCos-decreasing (fst construction)
      (characterizedHalfPi-quarterTurn construction) (snd construction)
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcSin-strictlyIncreasing : ∀ left right → fst left <ℝ fst right →
    fst (characterizedArcSin construction intermediate left) <ℝ
    fst (characterizedArcSin construction intermediate right)
  characterizedArcSin-strictlyIncreasing =
    restrictedArcSin-strictlyIncreasing (fst construction)
      (characterizedHalfPi-quarterTurn construction) (snd construction)
      (characterizedRestrictedSine-isEquiv construction intermediate)

  characterizedArcCos-strictlyDecreasing : ∀ left right → fst left <ℝ fst right →
    fst (characterizedArcCos construction intermediate right) <ℝ
    fst (characterizedArcCos construction intermediate left)
  characterizedArcCos-strictlyDecreasing =
    restrictedArcCos-strictlyDecreasing (fst construction)
      (characterizedHalfPi-quarterTurn construction) (snd construction)
      (characterizedRestrictedSine-isEquiv construction intermediate)

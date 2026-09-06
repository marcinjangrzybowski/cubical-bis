module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.RestrictedSine where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
  using (firstPositiveCosineZero-positive)

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Definition
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.QuarterTurn
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction


CharacterizedHalfPiSineStrictlyIncreasing :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiSineStrictlyIncreasing construction =
  SineQuarterStrictlyIncreasing (fst construction)


CharacterizedHalfPiSineIntermediateValue :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiSineIntermediateValue construction =
  SineQuarterIntermediateValue (fst construction)


-- The characterization supplies both orientation and strict monotonicity.
-- Only the intermediate-value obligation remains for the equivalence.
characterizedRestrictedSine-isEquiv :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineIntermediateValue construction →
  isEquiv (restrictedSine (fst construction))
characterizedRestrictedSine-isEquiv construction intermediate =
  restrictedSine-isEquivFromIntermediateValue
    (fst construction) (characterizedHalfPi-quarterTurn construction)
    (snd construction) intermediate


characterizedRestrictedSineEquiv :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineIntermediateValue construction →
  SineQuarterInterval (fst construction) ≃ SineUnitInterval
characterizedRestrictedSineEquiv construction intermediate =
  restrictedSine (fst construction)
  , characterizedRestrictedSine-isEquiv construction intermediate


characterizedRestrictedCosineEquiv :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineIntermediateValue construction →
  CosineHalfInterval (fst construction) ≃ SineUnitInterval
characterizedRestrictedCosineEquiv construction intermediate =
  restrictedCosineEquivFromSine (fst construction)
    (characterizedHalfPi-quarterTurn construction)
    (characterizedRestrictedSine-isEquiv construction intermediate)


CharacterizedHalfPiSineApproximateIntermediateValue :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiSineApproximateIntermediateValue construction =
  SineQuarterApproximateIntermediateValue (fst construction)


CharacterizedHalfPiSineImageApproximateIntermediateValue :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiSineImageApproximateIntermediateValue construction =
  SineQuarterImageApproximateIntermediateValue (fst construction)


CharacterizedHalfPiSineApproximateImageDensity :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiSineApproximateImageDensity construction =
  SineQuarterApproximateImageDensity (fst construction)


-- Finite bisection gives approximate density, not an exact inverse.
characterizedHalfPi-sineApproximateImageDensity :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineApproximateImageDensity construction
characterizedHalfPi-sineApproximateImageDensity construction =
  sineQuarterApproximateImageDensityByBisection
    (fst construction) (characterizedHalfPi-quarterTurn construction)
    (<ℝ-weaken 0ℝ (fst construction)
      (firstPositiveCosineZero-positive (snd construction)))


CharacterizedHalfPiRationalSineInverseData :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiRationalSineInverseData construction =
  RationalSineInverseData (fst construction)


CharacterizedHalfPiRationalSineInverseConstruction :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiRationalSineInverseConstruction construction =
  RationalSineInverseConstruction (fst construction)


CharacterizedHalfPiRationalSineInverseApproximationFamily :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiRationalSineInverseApproximationFamily construction =
  RationalSineInverseApproximationFamily (fst construction)


CharacterizedHalfPiMereRationalSineInverseApproximationFamily :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiMereRationalSineInverseApproximationFamily construction =
  MereRationalSineInverseApproximationFamily (fst construction)


CharacterizedHalfPiRationalPointSineInverseApproximationFamily :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiRationalPointSineInverseApproximationFamily construction =
  RationalPointSineInverseApproximationFamily (fst construction)


CharacterizedHalfPiRationalPointSineInverseImageApproximationFamily :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiRationalPointSineInverseImageApproximationFamily
    construction =
  RationalPointSineInverseImageApproximationFamily (fst construction)


characterizedRestrictedSine-isEquivFromBoundaries :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineStrictlyIncreasing construction →
  CharacterizedHalfPiSineIntermediateValue construction →
  isEquiv (restrictedSine (fst construction))
characterizedRestrictedSine-isEquivFromBoundaries
    construction strictly-increasing intermediate =
  restrictedSine-isEquivFromStrictIncreaseAndIntermediateValue
    (fst construction) strictly-increasing intermediate


characterizedRestrictedSineEquivFromBoundaries :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineStrictlyIncreasing construction →
  CharacterizedHalfPiSineIntermediateValue construction →
  SineQuarterInterval (fst construction) ≃ SineUnitInterval
characterizedRestrictedSineEquivFromBoundaries
    construction strictly-increasing intermediate =
  restrictedSine (fst construction)
  , characterizedRestrictedSine-isEquivFromBoundaries
    construction strictly-increasing intermediate


characterizedRestrictedSine-isEmbedding :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineOne construction →
  isEmbedding (restrictedSine (fst construction))
characterizedRestrictedSine-isEmbedding construction sine-one =
  restrictedSine-isEmbedding
    (fst construction)
    (characterizedHalfPi-positiveQuarterTurn construction sine-one)
    (snd construction)


characterizedRestrictedSine-isEquivFromIntermediateValue :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineOne construction →
  CharacterizedHalfPiSineIntermediateValue construction →
  isEquiv (restrictedSine (fst construction))
characterizedRestrictedSine-isEquivFromIntermediateValue
    construction sine-one intermediate =
  restrictedSine-isEquivFromIntermediateValue
    (fst construction)
    (characterizedHalfPi-positiveQuarterTurn construction sine-one)
    (snd construction)
    intermediate


characterizedRestrictedSineEquivFromIntermediateValue :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineOne construction →
  CharacterizedHalfPiSineIntermediateValue construction →
  SineQuarterInterval (fst construction) ≃ SineUnitInterval
characterizedRestrictedSineEquivFromIntermediateValue
    construction sine-one intermediate =
  restrictedSine (fst construction)
  , characterizedRestrictedSine-isEquivFromIntermediateValue
    construction sine-one intermediate


characterizedRestrictedSine-isEquivFromApproximateIntermediateValue :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineOne construction →
  CharacterizedHalfPiSineApproximateIntermediateValue construction →
  isEquiv (restrictedSine (fst construction))
characterizedRestrictedSine-isEquivFromApproximateIntermediateValue
    construction sine-one approximate =
  restrictedSine-isEquivFromApproximateIntermediateValue
    (fst construction)
    (characterizedHalfPi-positiveQuarterTurn construction sine-one)
    (snd construction)
    approximate


characterizedRestrictedSineEquivFromApproximateIntermediateValue :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineOne construction →
  CharacterizedHalfPiSineApproximateIntermediateValue construction →
  SineQuarterInterval (fst construction) ≃ SineUnitInterval
characterizedRestrictedSineEquivFromApproximateIntermediateValue
    construction sine-one approximate =
  restrictedSine (fst construction)
  , characterizedRestrictedSine-isEquivFromApproximateIntermediateValue
    construction sine-one approximate




characterizedRestrictedSine-isEquivFromRationalInverse :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineOne construction →
  CharacterizedHalfPiRationalSineInverseData construction →
  isEquiv (restrictedSine (fst construction))
characterizedRestrictedSine-isEquivFromRationalInverse
    construction sine-one inverse-data =
  restrictedSine-isEquivFromRationalInverse
    (fst construction)
    (characterizedHalfPi-positiveQuarterTurn construction sine-one)
    (snd construction)
    inverse-data


characterizedRestrictedSineEquivFromRationalInverse :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineOne construction →
  CharacterizedHalfPiRationalSineInverseData construction →
  SineQuarterInterval (fst construction) ≃ SineUnitInterval
characterizedRestrictedSineEquivFromRationalInverse
    construction sine-one inverse-data =
  restrictedSine (fst construction)
  , characterizedRestrictedSine-isEquivFromRationalInverse
    construction sine-one inverse-data


characterizedRestrictedSine-isEquivFromRationalConstruction :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineOne construction →
  MereChosenQuarterTurnSineClosenessReflectionModulus
    (fst construction) →
  CharacterizedHalfPiRationalSineInverseConstruction construction →
  isEquiv (restrictedSine (fst construction))
characterizedRestrictedSine-isEquivFromRationalConstruction
    construction sine-one modulus inverse-construction =
  restrictedSine-isEquivFromRationalConstruction
    (fst construction)
    (characterizedHalfPi-positiveQuarterTurn construction sine-one)
    (snd construction)
    modulus inverse-construction


characterizedRestrictedSineEquivFromRationalConstruction :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineOne construction →
  MereChosenQuarterTurnSineClosenessReflectionModulus
    (fst construction) →
  CharacterizedHalfPiRationalSineInverseConstruction construction →
  SineQuarterInterval (fst construction) ≃ SineUnitInterval
characterizedRestrictedSineEquivFromRationalConstruction
    construction sine-one modulus inverse-construction =
  restrictedSine (fst construction)
  , characterizedRestrictedSine-isEquivFromRationalConstruction
    construction sine-one modulus inverse-construction

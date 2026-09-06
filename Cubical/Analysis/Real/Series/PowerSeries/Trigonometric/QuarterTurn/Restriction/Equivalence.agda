module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Monotonicity
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Surjectivity
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation


restrictedSine-isEquivFromEmbeddingAndIntermediateValue :
  ∀ quarter →
  isEmbedding (restrictedSine quarter) →
  SineQuarterIntermediateValue quarter →
  isEquiv (restrictedSine quarter)
restrictedSine-isEquivFromEmbeddingAndIntermediateValue
    quarter embedding intermediate =
  isEmbedding×isSurjection→isEquiv
    ( embedding
    , sineQuarterIntermediateValue→restrictedSineSurjective
        quarter intermediate
    )


restrictedSineEquivFromEmbeddingAndIntermediateValue :
  ∀ quarter →
  isEmbedding (restrictedSine quarter) →
  SineQuarterIntermediateValue quarter →
  SineQuarterInterval quarter ≃ SineUnitInterval
restrictedSineEquivFromEmbeddingAndIntermediateValue
    quarter embedding intermediate =
  restrictedSine quarter
  , restrictedSine-isEquivFromEmbeddingAndIntermediateValue
      quarter embedding intermediate


restrictedSine-isEquivFromStrictIncreaseAndIntermediateValue :
  ∀ quarter →
  SineQuarterStrictlyIncreasing quarter →
  SineQuarterIntermediateValue quarter →
  isEquiv (restrictedSine quarter)
restrictedSine-isEquivFromStrictIncreaseAndIntermediateValue
    quarter strictly-increasing intermediate =
  restrictedSine-isEquivFromEmbeddingAndIntermediateValue
    quarter
    (restrictedSine-isEmbeddingFromStrictIncrease
      quarter strictly-increasing)
    intermediate


restrictedSineEquivFromStrictIncreaseAndIntermediateValue :
  ∀ quarter →
  SineQuarterStrictlyIncreasing quarter →
  SineQuarterIntermediateValue quarter →
  SineQuarterInterval quarter ≃ SineUnitInterval
restrictedSineEquivFromStrictIncreaseAndIntermediateValue
    quarter strictly-increasing intermediate =
  restrictedSine quarter
  , restrictedSine-isEquivFromStrictIncreaseAndIntermediateValue
      quarter strictly-increasing intermediate


restrictedSine-isEquivFromIntermediateValue :
  ∀ quarter →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  SineQuarterIntermediateValue quarter →
  isEquiv (restrictedSine quarter)
restrictedSine-isEquivFromIntermediateValue
    quarter positive-quarter characterization intermediate =
  restrictedSine-isEquivFromEmbeddingAndIntermediateValue
    quarter
    (restrictedSine-isEmbedding
      quarter positive-quarter characterization)
    intermediate


restrictedSineEquivFromIntermediateValue :
  ∀ quarter →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  SineQuarterIntermediateValue quarter →
  SineQuarterInterval quarter ≃ SineUnitInterval
restrictedSineEquivFromIntermediateValue
    quarter positive-quarter characterization intermediate =
  restrictedSine quarter
  , restrictedSine-isEquivFromIntermediateValue
      quarter positive-quarter characterization intermediate


restrictedSine-isEquivFromApproximateIntermediateValue :
  ∀ quarter →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  SineQuarterApproximateIntermediateValue quarter →
  isEquiv (restrictedSine quarter)
restrictedSine-isEquivFromApproximateIntermediateValue
    quarter positive-quarter characterization approximate =
  restrictedSine-isEquivFromIntermediateValue
    quarter positive-quarter characterization
    (sineQuarterApproximateIntermediateValue→intermediateValue
      quarter approximate)


restrictedSineEquivFromApproximateIntermediateValue :
  ∀ quarter →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  SineQuarterApproximateIntermediateValue quarter →
  SineQuarterInterval quarter ≃ SineUnitInterval
restrictedSineEquivFromApproximateIntermediateValue
    quarter positive-quarter characterization approximate =
  restrictedSine quarter
  , restrictedSine-isEquivFromApproximateIntermediateValue
      quarter positive-quarter characterization approximate




restrictedSine-isEquivFromRationalInverse :
  ∀ quarter →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  RationalSineInverseData quarter →
  isEquiv (restrictedSine quarter)
restrictedSine-isEquivFromRationalInverse
    quarter positive-quarter characterization inverse-data =
  restrictedSine-isEquivFromIntermediateValue
    quarter positive-quarter characterization
    (rationalSineInverseData→intermediateValue
      quarter inverse-data)


restrictedSineEquivFromRationalInverse :
  ∀ quarter →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  RationalSineInverseData quarter →
  SineQuarterInterval quarter ≃ SineUnitInterval
restrictedSineEquivFromRationalInverse
    quarter positive-quarter characterization inverse-data =
  restrictedSine quarter
  , restrictedSine-isEquivFromRationalInverse
      quarter positive-quarter characterization inverse-data


restrictedSine-isEquivFromRationalConstruction :
  ∀ quarter →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  MereChosenQuarterTurnSineClosenessReflectionModulus quarter →
  RationalSineInverseConstruction quarter →
  isEquiv (restrictedSine quarter)
restrictedSine-isEquivFromRationalConstruction
    quarter positive-quarter characterization modulus construction =
  restrictedSine-isEquivFromIntermediateValue
    quarter positive-quarter characterization
    (mereRationalSineInverseConstruction→intermediateValue
      quarter modulus construction)


restrictedSineEquivFromRationalConstruction :
  ∀ quarter →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  MereChosenQuarterTurnSineClosenessReflectionModulus quarter →
  RationalSineInverseConstruction quarter →
  SineQuarterInterval quarter ≃ SineUnitInterval
restrictedSineEquivFromRationalConstruction
    quarter positive-quarter characterization modulus construction =
  restrictedSine quarter
  , restrictedSine-isEquivFromRationalConstruction
      quarter positive-quarter characterization modulus construction

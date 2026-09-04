module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Modulus
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base
  public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Closeness
  public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Ordered
  public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Absolute
  public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Radius
  public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Build
  public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Sequence
  public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Choice
  public


open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/4₊)


opaque
  characterizedQuarterTurn-sineClosenessReflectionModulus :
    ∀ (quarter : ℝ) →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    QuarterTurnSineClosenessReflectionModulus quarter
  characterizedQuarterTurn-sineClosenessReflectionModulus
      quarter positive-quarter characterization input =
    orderedSineSeparationModulusBelowRadius→closenessReflectionModulus
      quarter (input /4₊) input
      (quarterRadiusDouble<radius input)
      (characterizedQuarterTurn-orderedSineSeparationModulus
        quarter positive-quarter characterization (input /4₊))


  characterizedQuarterTurn-mereChosenSineClosenessReflectionModulus :
    ∀ quarter →
    PositiveRationalChoice₀ →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    MereChosenQuarterTurnSineClosenessReflectionModulus quarter
  characterizedQuarterTurn-mereChosenSineClosenessReflectionModulus
      quarter choice positive-quarter characterization =
    positiveRationalChoice→mereChosenSineClosenessReflectionModulus
      quarter choice
      (characterizedQuarterTurn-sineClosenessReflectionModulus
        quarter positive-quarter characterization)

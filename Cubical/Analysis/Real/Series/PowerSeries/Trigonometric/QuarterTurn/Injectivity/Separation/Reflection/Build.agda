module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Build where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Modulus
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Absolute
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Radius


open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/4₊)


opaque
  orderedSineSeparationBelowRadius→closenessReflection :
    ∀ (quarter : ℝ) (small input output : ℚ₊) →
    rat (fst small) + rat (fst small) <ℝ rat (fst input) →
    QuarterTurnOrderedSineSeparation quarter small output →
    QuarterTurnSineClosenessReflection quarter input output
  orderedSineSeparationBelowRadius→closenessReflection
      quarter small input output double-small<input
      separate left right image-close =
    doubledRadiusAbsoluteBound→closeness
      small input (fst left) (fst right)
      double-small<input absolute-bound
    where
    absolute-bound :
      absℝ (fst left - fst right)
        ≤ℝ
      rat (fst small) + rat (fst small)
    absolute-bound =
      quarterTurnOrderedSeparation-reflectsAbsoluteDifference
        quarter small output separate left right image-close


  orderedSineSeparationModulusBelowRadius→closenessReflectionModulus :
    ∀ (quarter : ℝ) (small input : ℚ₊) →
    rat (fst small) + rat (fst small) <ℝ rat (fst input) →
    ∥ Σ[ output ∈ ℚ₊ ]
        QuarterTurnOrderedSineSeparation quarter small output ∥₁ →
    ∥ Σ[ output ∈ ℚ₊ ]
        QuarterTurnSineClosenessReflection quarter input output ∥₁
  orderedSineSeparationModulusBelowRadius→closenessReflectionModulus
      quarter small input double-small<input =
    PT.map λ (output , separate) →
      output ,
      orderedSineSeparationBelowRadius→closenessReflection
        quarter small input output double-small<input separate

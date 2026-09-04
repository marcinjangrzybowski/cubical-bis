module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base


open PositiveRationals using (ℚ₊)


QuarterTurnSineClosenessReflection : ℝ → ℚ₊ → ℚ₊ → Type₀
QuarterTurnSineClosenessReflection quarter input output =
  ∀ (left right : SineQuarterInterval quarter) →
  sinℝ (fst left) ∼[ output ] sinℝ (fst right) →
  fst left ∼[ input ] fst right


QuarterTurnSineClosenessReflectionModulus : ℝ → Type₀
QuarterTurnSineClosenessReflectionModulus quarter =
  ∀ input →
  ∥ Σ[ output ∈ ℚ₊ ]
      QuarterTurnSineClosenessReflection quarter input output ∥₁


ChosenQuarterTurnSineClosenessReflectionModulus : ℝ → Type₀
ChosenQuarterTurnSineClosenessReflectionModulus quarter =
  ∀ input →
  Σ[ output ∈ ℚ₊ ]
    QuarterTurnSineClosenessReflection quarter input output


MereChosenQuarterTurnSineClosenessReflectionModulus : ℝ → Type₀
MereChosenQuarterTurnSineClosenessReflectionModulus quarter =
  ∥ ChosenQuarterTurnSineClosenessReflectionModulus quarter ∥₁

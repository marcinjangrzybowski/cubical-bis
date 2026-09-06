module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Monotonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Monotonicity
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Inverse


opaque
  restrictedArcSin-increasingFromStrictIncrease : ∀ quarter →
    SineQuarterStrictlyIncreasing quarter → ∀ equivalent left right →
    fst left ≤ℝ fst right →
    fst (restrictedArcSin quarter equivalent left) ≤ℝ
    fst (restrictedArcSin quarter equivalent right)
  restrictedArcSin-increasingFromStrictIncrease
      quarter strictly-increasing equivalent left right left≤right =
    notGreater→≤ℝ
      (fst (restrictedArcSin quarter equivalent left))
      (fst (restrictedArcSin quarter equivalent right)) λ reversed →
    ≤ℝ→≯ (fst left) (fst right) left≤right
      (subst2 _<ℝ_
        (sinℝ-restrictedArcSin quarter equivalent right)
        (sinℝ-restrictedArcSin quarter equivalent left)
        (strictly-increasing
          (restrictedArcSin quarter equivalent right)
          (restrictedArcSin quarter equivalent left) reversed))

  restrictedArcCos-decreasingFromStrictIncrease : ∀ quarter →
    SineQuarterStrictlyIncreasing quarter → ∀ equivalent left right →
    fst left ≤ℝ fst right →
    fst (restrictedArcCos quarter equivalent right) ≤ℝ
    fst (restrictedArcCos quarter equivalent left)
  restrictedArcCos-decreasingFromStrictIncrease
      quarter strictly-increasing equivalent left right left≤right =
    subst2 _≤ℝ_
      (sym (restrictedArcCos-value quarter equivalent right))
      (sym (restrictedArcCos-value quarter equivalent left))
      (addPres≤L
        (- fst (restrictedArcSin quarter equivalent right))
        (- fst (restrictedArcSin quarter equivalent left)) quarter
        (negPres≤
          (fst (restrictedArcSin quarter equivalent left))
          (fst (restrictedArcSin quarter equivalent right))
          (restrictedArcSin-increasingFromStrictIncrease
            quarter strictly-increasing equivalent left right left≤right)))


restrictedArcSin-increasing : ∀ quarter →
  IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
  ∀ equivalent left right → fst left ≤ℝ fst right →
  fst (restrictedArcSin quarter equivalent left) ≤ℝ
  fst (restrictedArcSin quarter equivalent right)
restrictedArcSin-increasing quarter positive-quarter characterization =
  restrictedArcSin-increasingFromStrictIncrease quarter
    (restrictedSine-strictlyIncreasing quarter positive-quarter characterization)

restrictedArcCos-decreasing : ∀ quarter →
  IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
  ∀ equivalent left right → fst left ≤ℝ fst right →
  fst (restrictedArcCos quarter equivalent right) ≤ℝ
  fst (restrictedArcCos quarter equivalent left)
restrictedArcCos-decreasing quarter positive-quarter characterization =
  restrictedArcCos-decreasingFromStrictIncrease quarter
    (restrictedSine-strictlyIncreasing quarter positive-quarter characterization)

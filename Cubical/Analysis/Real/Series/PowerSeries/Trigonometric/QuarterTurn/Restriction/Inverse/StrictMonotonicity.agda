module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.StrictMonotonicity where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Continuity
  using (continuousReflectsStrictOnOrderedInputs)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Monotonicity
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Monotonicity
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Inverse

opaque
  restrictedArcSin-strictlyIncreasingFromStrictIncrease : ∀ quarter →
    SineQuarterStrictlyIncreasing quarter → ∀ equivalent left right →
    fst left <ℝ fst right →
    fst (restrictedArcSin quarter equivalent left) <ℝ
    fst (restrictedArcSin quarter equivalent right)
  restrictedArcSin-strictlyIncreasingFromStrictIncrease
      quarter strictly-increasing equivalent left right left<right =
    continuousReflectsStrictOnOrderedInputs sinℝ sinℝIsContinuous
      (fst (restrictedArcSin quarter equivalent left))
      (fst (restrictedArcSin quarter equivalent right))
      (restrictedArcSin-increasingFromStrictIncrease
        quarter strictly-increasing equivalent left right
        (<ℝ-weaken (fst left) (fst right) left<right))
      (subst2 _<ℝ_
        (sym (sinℝ-restrictedArcSin quarter equivalent left))
        (sym (sinℝ-restrictedArcSin quarter equivalent right)) left<right)

  restrictedArcCos-strictlyDecreasingFromStrictIncrease : ∀ quarter →
    SineQuarterStrictlyIncreasing quarter → ∀ equivalent left right →
    fst left <ℝ fst right →
    fst (restrictedArcCos quarter equivalent right) <ℝ
    fst (restrictedArcCos quarter equivalent left)
  restrictedArcCos-strictlyDecreasingFromStrictIncrease
      quarter strictly-increasing equivalent left right left<right =
    subst2 _<ℝ_
      (sym (restrictedArcCos-value quarter equivalent right))
      (sym (restrictedArcCos-value quarter equivalent left))
      (<ℝ-addL
        (- fst (restrictedArcSin quarter equivalent right))
        (- fst (restrictedArcSin quarter equivalent left)) quarter
        (<ℝ-neg
          (fst (restrictedArcSin quarter equivalent left))
          (fst (restrictedArcSin quarter equivalent right))
          (restrictedArcSin-strictlyIncreasingFromStrictIncrease
            quarter strictly-increasing equivalent left right left<right)))


restrictedArcSin-strictlyIncreasing : ∀ quarter →
  IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
  ∀ equivalent left right → fst left <ℝ fst right →
  fst (restrictedArcSin quarter equivalent left) <ℝ
  fst (restrictedArcSin quarter equivalent right)
restrictedArcSin-strictlyIncreasing quarter positive-quarter characterization =
  restrictedArcSin-strictlyIncreasingFromStrictIncrease quarter
    (restrictedSine-strictlyIncreasing quarter positive-quarter characterization)

restrictedArcCos-strictlyDecreasing : ∀ quarter →
  IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
  ∀ equivalent left right → fst left <ℝ fst right →
  fst (restrictedArcCos quarter equivalent right) <ℝ
  fst (restrictedArcCos quarter equivalent left)
restrictedArcCos-strictlyDecreasing quarter positive-quarter characterization =
  restrictedArcCos-strictlyDecreasingFromStrictIncrease quarter
    (restrictedSine-strictlyIncreasing quarter positive-quarter characterization)

module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Ordered where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Located

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Modulus
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Closeness


open PositiveRationals using (ℚ₊)


opaque
  quarterTurnOrderedSeparation-reflectsUpperDifference :
    ∀ (quarter : ℝ) (input output : ℚ₊) →
    QuarterTurnOrderedSineSeparation quarter input output →
    ∀ (left right : SineQuarterInterval quarter) →
    sinℝ (fst left) ∼[ output ] sinℝ (fst right) →
    fst right - fst left
      ≤ℝ rat (fst input) + rat (fst input)
  quarterTurnOrderedSeparation-reflectsUpperDifference
      quarter input output separate left right image-close =
    notGreater→≤ℝ difference input-double difference-not-too-large
    where
    difference : ℝ
    difference = fst right - fst left

    input-double : ℝ
    input-double = rat (fst input) + rat (fst input)

    image-difference : ℝ
    image-difference = sinℝ (fst right) - sinℝ (fst left)

    difference-not-too-large : ¬ (input-double <ℝ difference)
    difference-not-too-large input-double<difference =
      <ℝ-irrefl (rat (fst output))
        (<≤ℝ-trans
          (rat (fst output)) image-difference (rat (fst output))
          (separate (fst left) (fst right)
            (fst (snd left)) (snd (snd right))
            (<ℝ-weaken input-double difference input-double<difference))
          (closeness→reverseDifference≤
            (sinℝ (fst left)) (sinℝ (fst right)) output image-close))

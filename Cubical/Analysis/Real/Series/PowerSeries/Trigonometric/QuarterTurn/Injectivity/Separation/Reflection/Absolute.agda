module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Absolute where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (addComm)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Modulus
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Ordered


open PositiveRationals using (ℚ₊)


private
  negSub : ∀ (x y : ℝ) → - (x - y) ≡ y - x
  negSub x y =
    negAdd x (- y)
    ∙ cong ((- x) +_) (negInvol y)
    ∙ addComm (- x) y


opaque
  quarterTurnOrderedSeparation-reflectsAbsoluteDifference :
    ∀ (quarter : ℝ) (input output : ℚ₊) →
    QuarterTurnOrderedSineSeparation quarter input output →
    ∀ (left right : SineQuarterInterval quarter) →
    sinℝ (fst left) ∼[ output ] sinℝ (fst right) →
    absℝ (fst left - fst right)
      ≤ℝ rat (fst input) + rat (fst input)
  quarterTurnOrderedSeparation-reflectsAbsoluteDifference
      quarter input output separate left right image-close =
    absLeastUpperBound
      (fst left - fst right) input-double
      left-minus-right≤input-double
      (subst (_≤ℝ input-double)
        (sym (negSub (fst left) (fst right)))
        right-minus-left≤input-double)
    where
    input-double : ℝ
    input-double = rat (fst input) + rat (fst input)

    right-minus-left≤input-double :
      fst right - fst left ≤ℝ input-double
    right-minus-left≤input-double =
      quarterTurnOrderedSeparation-reflectsUpperDifference
        quarter input output separate left right image-close

    left-minus-right≤input-double :
      fst left - fst right ≤ℝ input-double
    left-minus-right≤input-double =
      quarterTurnOrderedSeparation-reflectsUpperDifference
        quarter input output separate right left
        (sym∼
          (sinℝ (fst left)) (sinℝ (fst right)) output image-close)

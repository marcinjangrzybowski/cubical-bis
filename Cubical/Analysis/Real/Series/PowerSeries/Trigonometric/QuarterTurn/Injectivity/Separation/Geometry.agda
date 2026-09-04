module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Geometry where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry


private
  addSubCancel : ∀ x y → (x - y) + y ≡ x
  addSubCancel x y =
    sym (addAssoc x (- y) y)
    ∙ cong (x +_) (addInvL y)
    ∙ addIdR x


  reorderedAddSubCancel : ∀ x y → y + (x - y) ≡ x
  reorderedAddSubCancel x y =
    addComm y (x - y)
    ∙ addSubCancel x y


  negativeMidpoint-plusHalfDifference : ∀ x y →
    (- quarterTurnMidpoint x y) + quarterTurnHalfDifference x y
      ≡ - x
  negativeMidpoint-plusHalfDifference x y =
    cong ((- quarterTurnMidpoint x y) +_)
      (sym (negInvol (quarterTurnHalfDifference x y)))
    ∙ sym
        (negAdd
          (quarterTurnMidpoint x y)
          (- quarterTurnHalfDifference x y))
    ∙ cong -_
        (quarterTurnMidpoint-plusNegativeHalfDifference x y)


opaque
  quarterTurnHalfDifference-plusAbsMidpoint≤quarter :
    ∀ quarter x y →
    (- quarter) ≤ℝ x → y ≤ℝ quarter →
    quarterTurnHalfDifference x y +
      absℝ (quarterTurnMidpoint x y)
      ≤ℝ quarter
  quarterTurnHalfDifference-plusAbsMidpoint≤quarter
      quarter x y negative-quarter≤x y≤quarter =
    subst
      ((quarterTurnHalfDifference x y +
        absℝ (quarterTurnMidpoint x y)) ≤ℝ_)
      (reorderedAddSubCancel quarter (quarterTurnHalfDifference x y))
      (addPres≤L
        (absℝ (quarterTurnMidpoint x y))
        (quarter - quarterTurnHalfDifference x y)
        (quarterTurnHalfDifference x y)
        absolute-midpoint≤remainder)
    where
    midpoint≤remainder :
      quarterTurnMidpoint x y
        ≤ℝ quarter - quarterTurnHalfDifference x y
    midpoint≤remainder =
      addReflects≤R
        (quarterTurnMidpoint x y)
        (quarter - quarterTurnHalfDifference x y)
        (quarterTurnHalfDifference x y)
        (subst2 _≤ℝ_
          (sym (quarterTurnMidpoint-plusHalfDifference x y))
          (sym (addSubCancel quarter (quarterTurnHalfDifference x y)))
          y≤quarter)

    negative-x≤quarter : (- x) ≤ℝ quarter
    negative-x≤quarter =
      subst ((- x) ≤ℝ_)
        (negInvol quarter)
        (negPres≤ (- quarter) x negative-quarter≤x)

    negative-midpoint≤remainder :
      (- quarterTurnMidpoint x y)
        ≤ℝ quarter - quarterTurnHalfDifference x y
    negative-midpoint≤remainder =
      addReflects≤R
        (- quarterTurnMidpoint x y)
        (quarter - quarterTurnHalfDifference x y)
        (quarterTurnHalfDifference x y)
        (subst2 _≤ℝ_
          (sym (negativeMidpoint-plusHalfDifference x y))
          (sym (addSubCancel quarter (quarterTurnHalfDifference x y)))
          negative-x≤quarter)

    absolute-midpoint≤remainder :
      absℝ (quarterTurnMidpoint x y)
        ≤ℝ quarter - quarterTurnHalfDifference x y
    absolute-midpoint≤remainder =
      absLeastUpperBound
        (quarterTurnMidpoint x y)
        (quarter - quarterTurnHalfDifference x y)
        midpoint≤remainder negative-midpoint≤remainder


  quarterTurnHalfDifference≤quarterMinusAbsMidpoint :
    ∀ quarter x y →
    (- quarter) ≤ℝ x → y ≤ℝ quarter →
    quarterTurnHalfDifference x y
      ≤ℝ quarter - absℝ (quarterTurnMidpoint x y)
  quarterTurnHalfDifference≤quarterMinusAbsMidpoint
      quarter x y negative-quarter≤x y≤quarter =
    addReflects≤R
      (quarterTurnHalfDifference x y)
      (quarter - absℝ (quarterTurnMidpoint x y))
      (absℝ (quarterTurnMidpoint x y))
      (subst
        ((quarterTurnHalfDifference x y +
          absℝ (quarterTurnMidpoint x y)) ≤ℝ_)
        (sym (addSubCancel quarter
          (absℝ (quarterTurnMidpoint x y))))
        (quarterTurnHalfDifference-plusAbsMidpoint≤quarter
          quarter x y negative-quarter≤x y≤quarter))

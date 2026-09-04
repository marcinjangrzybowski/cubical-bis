module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition

open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry


opaque
  quarterTurnMidpoint-inside : ∀ (quarter x y : ℝ) →
    (- quarter) ≤ℝ x → y ≤ℝ quarter → x <ℝ y →
    ((- quarter) <ℝ quarterTurnMidpoint x y)
    × (quarterTurnMidpoint x y <ℝ quarter)
  quarterTurnMidpoint-inside
      quarter x y negative-quarter≤x y≤quarter x<y =
    midpoint-lower , midpoint-upper
    where
    negative-quarter<y : (- quarter) <ℝ y
    negative-quarter<y =
      ≤<ℝ-trans (- quarter) x y negative-quarter≤x x<y

    lower-sum :
      ((- quarter) + (- quarter)) <ℝ x + y
    lower-sum =
      ≤<ℝ-add
        (- quarter) x (- quarter) y
        negative-quarter≤x negative-quarter<y

    midpoint-lower : (- quarter) <ℝ quarterTurnMidpoint x y
    midpoint-lower =
      subst ( _<ℝ quarterTurnMidpoint x y)
        (quarterTurnHalfScalar-double (- quarter))
        (quarterTurnHalfScalar-pres<
          {x = (- quarter) + (- quarter)}
          {y = x + y}
          lower-sum)

    x<quarter : x <ℝ quarter
    x<quarter =
      <≤ℝ-trans x y quarter x<y y≤quarter

    upper-sum : x + y <ℝ quarter + quarter
    upper-sum =
      <≤ℝ-add x quarter y quarter
        x<quarter y≤quarter

    midpoint-upper : quarterTurnMidpoint x y <ℝ quarter
    midpoint-upper =
      subst (quarterTurnMidpoint x y <ℝ_)
        (quarterTurnHalfScalar-double quarter)
        (quarterTurnHalfScalar-pres<
          {x = x + y}
          {y = quarter + quarter}
          upper-sum)


opaque
  quarterTurnHalfDifference≤quarter : ∀ (quarter x y : ℝ) →
    (- quarter) ≤ℝ x → y ≤ℝ quarter →
    quarterTurnHalfDifference x y ≤ℝ quarter
  quarterTurnHalfDifference≤quarter
      quarter x y negative-quarter≤x y≤quarter =
    subst (quarterTurnHalfDifference x y ≤ℝ_)
      (quarterTurnHalfScalar-double quarter)
      (quarterTurnHalfScalar-pres≤
        {x = y - x}
        {y = quarter + quarter}
        difference≤double-quarter)
    where
    negative-x≤quarter : (- x) ≤ℝ quarter
    negative-x≤quarter =
      subst ((- x) ≤ℝ_)
        (negInvol quarter)
        (negPres≤ (- quarter) x negative-quarter≤x)

    difference≤double-quarter :
      y - x ≤ℝ quarter + quarter
    difference≤double-quarter =
      addPres≤ y quarter (- x) quarter
        y≤quarter negative-x≤quarter

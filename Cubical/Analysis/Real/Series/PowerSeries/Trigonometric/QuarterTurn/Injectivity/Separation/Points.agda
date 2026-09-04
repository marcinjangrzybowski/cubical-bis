module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Points where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ; addIdR)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negZero)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Bounds
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Geometry


open PositiveRationals using (ℚ₊)


opaque
  negativeQuarter≤zero : ∀ quarter →
    0ℝ <ℝ quarter → (- quarter) ≤ℝ 0ℝ
  negativeQuarter≤zero quarter zero<quarter =
    <ℝ-weaken (- quarter) 0ℝ
      (subst ((- quarter) <ℝ_)
        negZero (<ℝ-neg 0ℝ quarter zero<quarter))


  positiveRational-real-positive : ∀ (probe : ℚ₊) →
    0ℝ <ℝ rat (fst probe)
  positiveRational-real-positive probe =
    <ℚ→<ℝ 0 (fst probe) (snd probe)


  quarterTurnSeparationProbe≤quarter :
    ∀ (quarter : ℝ) (probe : ℚ₊) (x y : ℝ) →
    (- quarter) ≤ℝ x → y ≤ℝ quarter →
    rat (fst probe) <ℝ quarterTurnHalfDifference x y →
    rat (fst probe) ≤ℝ quarter
  quarterTurnSeparationProbe≤quarter
      quarter probe x y negative-quarter≤x y≤quarter probe<difference =
    <ℝ-weaken (rat (fst probe)) quarter
      (<≤ℝ-trans
        (rat (fst probe)) (quarterTurnHalfDifference x y) quarter
        probe<difference
        (quarterTurnHalfDifference≤quarter
          quarter x y negative-quarter≤x y≤quarter))


  quarterTurnSeparationProbePoint :
    ∀ (quarter : ℝ) (probe : ℚ₊) (x y : ℝ) →
    0ℝ <ℝ quarter →
    (- quarter) ≤ℝ x → y ≤ℝ quarter →
    rat (fst probe) <ℝ quarterTurnHalfDifference x y →
    SineQuarterInterval quarter
  quarterTurnSeparationProbePoint
      quarter probe x y zero<quarter
      negative-quarter≤x y≤quarter probe<difference =
    rat (fst probe)
    , ≤ℝ-trans (- quarter) 0ℝ (rat (fst probe))
        (negativeQuarter≤zero quarter zero<quarter)
        (<ℝ-weaken 0ℝ (rat (fst probe))
          (positiveRational-real-positive probe))
    , quarterTurnSeparationProbe≤quarter
        quarter probe x y negative-quarter≤x y≤quarter
        probe<difference


  quarterTurnSeparationDifferencePoint : ∀ (quarter x y : ℝ) →
    0ℝ <ℝ quarter →
    (- quarter) ≤ℝ x → y ≤ℝ quarter → x <ℝ y →
    SineQuarterInterval quarter
  quarterTurnSeparationDifferencePoint
      quarter x y zero<quarter negative-quarter≤x y≤quarter x<y =
    quarterTurnHalfDifference x y
    , ≤ℝ-trans (- quarter) 0ℝ (quarterTurnHalfDifference x y)
        (negativeQuarter≤zero quarter zero<quarter)
        (<ℝ-weaken 0ℝ (quarterTurnHalfDifference x y)
          (quarterTurnHalfDifference-positive x y x<y))
    , quarterTurnHalfDifference≤quarter
        quarter x y negative-quarter≤x y≤quarter


  quarterTurnSeparationProbe<remainder :
    ∀ (quarter : ℝ) (probe : ℚ₊) (x y : ℝ) →
    (- quarter) ≤ℝ x → y ≤ℝ quarter →
    rat (fst probe) <ℝ quarterTurnHalfDifference x y →
    rat (fst probe)
      <ℝ quarter + (- absℝ (quarterTurnMidpoint x y))
  quarterTurnSeparationProbe<remainder
      quarter probe x y negative-quarter≤x y≤quarter probe<difference =
    <≤ℝ-trans
      (rat (fst probe))
      (quarterTurnHalfDifference x y)
      (quarter + (- absℝ (quarterTurnMidpoint x y)))
      probe<difference
      (quarterTurnHalfDifference≤quarterMinusAbsMidpoint
        quarter x y negative-quarter≤x y≤quarter)


  quarterTurnSeparationRemainderPoint :
    ∀ (quarter : ℝ) (probe : ℚ₊) (x y : ℝ) →
    0ℝ <ℝ quarter →
    (- quarter) ≤ℝ x → y ≤ℝ quarter →
    rat (fst probe) <ℝ quarterTurnHalfDifference x y →
    SineQuarterInterval quarter
  quarterTurnSeparationRemainderPoint
      quarter probe x y zero<quarter
      negative-quarter≤x y≤quarter probe<difference =
    remainder
    , ≤ℝ-trans (- quarter) 0ℝ remainder
        (negativeQuarter≤zero quarter zero<quarter)
        (<ℝ-weaken 0ℝ remainder
          (<ℝ-trans 0ℝ (rat (fst probe)) remainder
            (positiveRational-real-positive probe) probe<remainder))
    , remainder≤quarter
    where
    remainder : ℝ
    remainder = quarter + (- absℝ (quarterTurnMidpoint x y))

    probe<remainder : rat (fst probe) <ℝ remainder
    probe<remainder =
      quarterTurnSeparationProbe<remainder
        quarter probe x y negative-quarter≤x y≤quarter probe<difference

    negative-abs≤zero : (- absℝ (quarterTurnMidpoint x y)) ≤ℝ 0ℝ
    negative-abs≤zero =
      subst ((- absℝ (quarterTurnMidpoint x y)) ≤ℝ_)
        negZero
        (negPres≤ 0ℝ (absℝ (quarterTurnMidpoint x y))
          (absNonnegative (quarterTurnMidpoint x y)))

    remainder≤quarter : remainder ≤ℝ quarter
    remainder≤quarter =
      subst (remainder ≤ℝ_)
        (addIdR quarter)
        (addPres≤L
          (- absℝ (quarterTurnMidpoint x y)) 0ℝ quarter
          negative-abs≤zero)


  quarterTurnSeparationProbePoint-value :
    ∀ (quarter : ℝ) (probe : ℚ₊) (x y : ℝ)
      (zero<quarter : 0ℝ <ℝ quarter)
      (negative-quarter≤x : (- quarter) ≤ℝ x)
      (y≤quarter : y ≤ℝ quarter)
      (probe<difference :
        rat (fst probe) <ℝ quarterTurnHalfDifference x y) →
    fst (quarterTurnSeparationProbePoint
      quarter probe x y zero<quarter
      negative-quarter≤x y≤quarter probe<difference)
      ≡ rat (fst probe)
  quarterTurnSeparationProbePoint-value
      quarter probe x y zero<quarter
      negative-quarter≤x y≤quarter probe<difference = refl


  quarterTurnSeparationDifferencePoint-value :
    ∀ (quarter x y : ℝ)
      (zero<quarter : 0ℝ <ℝ quarter)
      (negative-quarter≤x : (- quarter) ≤ℝ x)
      (y≤quarter : y ≤ℝ quarter)
      (x<y : x <ℝ y) →
    fst (quarterTurnSeparationDifferencePoint
      quarter x y zero<quarter negative-quarter≤x y≤quarter x<y)
      ≡ quarterTurnHalfDifference x y
  quarterTurnSeparationDifferencePoint-value
      quarter x y zero<quarter negative-quarter≤x y≤quarter x<y = refl


  quarterTurnSeparationRemainderPoint-value :
    ∀ (quarter : ℝ) (probe : ℚ₊) (x y : ℝ)
      (zero<quarter : 0ℝ <ℝ quarter)
      (negative-quarter≤x : (- quarter) ≤ℝ x)
      (y≤quarter : y ≤ℝ quarter)
      (probe<difference :
        rat (fst probe) <ℝ quarterTurnHalfDifference x y) →
    fst (quarterTurnSeparationRemainderPoint
      quarter probe x y zero<quarter
      negative-quarter≤x y≤quarter probe<difference)
      ≡ quarter + (- absℝ (quarterTurnMidpoint x y))
  quarterTurnSeparationRemainderPoint-value
      quarter probe x y zero<quarter
      negative-quarter≤x y≤quarter probe<difference = refl

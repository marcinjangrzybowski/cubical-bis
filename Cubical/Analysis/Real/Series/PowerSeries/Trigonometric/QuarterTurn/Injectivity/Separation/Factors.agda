module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Factors where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.SinePositive
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.CosineFactor
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Phase
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Points


open PositiveRationals using (ℚ₊)


opaque
  quarterTurnSeparationFloor-positive : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ (probe : ℚ₊) → rat (fst probe) ≤ℝ quarter →
    0ℝ <ℝ sinℝ (rat (fst probe))
  quarterTurnSeparationFloor-positive
      quarter positive-quarter characterization probe probe≤quarter =
    characterizedSine-positive-to-quarter
      quarter positive-quarter characterization
      (rat (fst probe))
      (positiveRational-real-positive probe)
      probe≤quarter


  quarterTurnSeparationFloor<differenceSine :
    ∀ (quarter : ℝ) →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ (probe : ℚ₊) (x y : ℝ) →
    (- quarter) ≤ℝ x → y ≤ℝ quarter → x <ℝ y →
    rat (fst probe) <ℝ quarterTurnHalfDifference x y →
    sinℝ (rat (fst probe))
      <ℝ sinℝ (quarterTurnHalfDifference x y)
  quarterTurnSeparationFloor<differenceSine
      quarter positive-quarter characterization probe x y
      negative-quarter≤x y≤quarter x<y probe<difference =
    subst2 _<ℝ_
      (cong sinℝ probe-point-value)
      (cong sinℝ difference-point-value)
      (sinℝ-strictMonotone-on-quarterInterval
        quarter positive-quarter characterization
        probe-point difference-point probe-point<difference-point)
    where
    zero<quarter : 0ℝ <ℝ quarter
    zero<quarter = firstPositiveCosineZero-positive characterization

    probe-point : SineQuarterInterval quarter
    probe-point =
      quarterTurnSeparationProbePoint
        quarter probe x y zero<quarter
        negative-quarter≤x y≤quarter probe<difference

    difference-point : SineQuarterInterval quarter
    difference-point =
      quarterTurnSeparationDifferencePoint
        quarter x y zero<quarter
        negative-quarter≤x y≤quarter x<y

    probe-point-value : fst probe-point ≡ rat (fst probe)
    probe-point-value =
      quarterTurnSeparationProbePoint-value
        quarter probe x y zero<quarter
        negative-quarter≤x y≤quarter probe<difference

    difference-point-value :
      fst difference-point ≡ quarterTurnHalfDifference x y
    difference-point-value =
      quarterTurnSeparationDifferencePoint-value
        quarter x y zero<quarter
        negative-quarter≤x y≤quarter x<y

    probe-point<difference-point :
      fst probe-point <ℝ fst difference-point
    probe-point<difference-point =
      subst2 _<ℝ_
        (sym (quarterTurnSeparationProbePoint-value
          quarter probe x y zero<quarter
          negative-quarter≤x y≤quarter probe<difference))
        (sym (quarterTurnSeparationDifferencePoint-value
          quarter x y zero<quarter
          negative-quarter≤x y≤quarter x<y))
        probe<difference


  quarterTurnSeparationFloor<remainderSine :
    ∀ (quarter : ℝ) →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ (probe : ℚ₊) (x y : ℝ) →
    (- quarter) ≤ℝ x → y ≤ℝ quarter →
    rat (fst probe) <ℝ quarterTurnHalfDifference x y →
    sinℝ (rat (fst probe))
      <ℝ sinℝ
        (quarter + (- absℝ (quarterTurnMidpoint x y)))
  quarterTurnSeparationFloor<remainderSine
      quarter positive-quarter characterization probe x y
      negative-quarter≤x y≤quarter probe<difference =
    subst2 _<ℝ_
      (cong sinℝ probe-point-value)
      (cong sinℝ remainder-point-value)
      (sinℝ-strictMonotone-on-quarterInterval
        quarter positive-quarter characterization
        probe-point remainder-point probe-point<remainder-point)
    where
    zero<quarter : 0ℝ <ℝ quarter
    zero<quarter = firstPositiveCosineZero-positive characterization

    probe-point : SineQuarterInterval quarter
    probe-point =
      quarterTurnSeparationProbePoint
        quarter probe x y zero<quarter
        negative-quarter≤x y≤quarter probe<difference

    remainder-point : SineQuarterInterval quarter
    remainder-point =
      quarterTurnSeparationRemainderPoint
        quarter probe x y zero<quarter
        negative-quarter≤x y≤quarter probe<difference

    probe-point-value : fst probe-point ≡ rat (fst probe)
    probe-point-value =
      quarterTurnSeparationProbePoint-value
        quarter probe x y zero<quarter
        negative-quarter≤x y≤quarter probe<difference

    remainder-point-value :
      fst remainder-point
        ≡ quarter + (- absℝ (quarterTurnMidpoint x y))
    remainder-point-value =
      quarterTurnSeparationRemainderPoint-value
        quarter probe x y zero<quarter
        negative-quarter≤x y≤quarter probe<difference

    probe-point<remainder-point :
      fst probe-point <ℝ fst remainder-point
    probe-point<remainder-point =
      subst2 _<ℝ_
        (sym (quarterTurnSeparationProbePoint-value
          quarter probe x y zero<quarter
          negative-quarter≤x y≤quarter probe<difference))
        (sym (quarterTurnSeparationRemainderPoint-value
          quarter probe x y zero<quarter
          negative-quarter≤x y≤quarter probe<difference))
        (quarterTurnSeparationProbe<remainder
          quarter probe x y negative-quarter≤x y≤quarter
          probe<difference)


  quarterTurnSeparationFloor<midpointCosine :
    ∀ (quarter : ℝ) →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ (probe : ℚ₊) (x y : ℝ) →
    (- quarter) ≤ℝ x → y ≤ℝ quarter →
    rat (fst probe) <ℝ quarterTurnHalfDifference x y →
    sinℝ (rat (fst probe))
      <ℝ cosℝ (quarterTurnMidpoint x y)
  quarterTurnSeparationFloor<midpointCosine
      quarter positive-quarter characterization probe x y
      negative-quarter≤x y≤quarter probe<difference =
    subst (sinℝ (rat (fst probe)) <ℝ_)
      (sym
        (quarterTurnMidpointCosine-asSineRemainder
          quarter positive-quarter x y))
      (quarterTurnSeparationFloor<remainderSine
        quarter positive-quarter characterization probe x y
        negative-quarter≤x y≤quarter probe<difference)


  quarterTurnSeparationFloorSquare<product :
    ∀ (quarter : ℝ) →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ (probe : ℚ₊) (x y : ℝ) →
    (- quarter) ≤ℝ x → y ≤ℝ quarter → x <ℝ y →
    rat (fst probe) <ℝ quarterTurnHalfDifference x y →
    sinℝ (rat (fst probe)) · sinℝ (rat (fst probe))
      <ℝ
    cosℝ (quarterTurnMidpoint x y)
      · sinℝ (quarterTurnHalfDifference x y)
  quarterTurnSeparationFloorSquare<product
      quarter positive-quarter characterization probe x y
      negative-quarter≤x y≤quarter x<y probe<difference =
    mulPres<
      floor (cosℝ (quarterTurnMidpoint x y))
      floor (sinℝ (quarterTurnHalfDifference x y))
      (quarterTurnMidpointCosinePositive
        quarter x y characterization
        negative-quarter≤x y≤quarter x<y)
      floor-positive
      (quarterTurnSeparationFloor<midpointCosine
        quarter positive-quarter characterization probe x y
        negative-quarter≤x y≤quarter probe<difference)
      (quarterTurnSeparationFloor<differenceSine
        quarter positive-quarter characterization probe x y
        negative-quarter≤x y≤quarter x<y probe<difference)
    where
    floor : ℝ
    floor = sinℝ (rat (fst probe))

    floor-positive : 0ℝ <ℝ floor
    floor-positive =
      quarterTurnSeparationFloor-positive
        quarter positive-quarter characterization probe
        (quarterTurnSeparationProbe≤quarter
          quarter probe x y negative-quarter≤x y≤quarter
          probe<difference)

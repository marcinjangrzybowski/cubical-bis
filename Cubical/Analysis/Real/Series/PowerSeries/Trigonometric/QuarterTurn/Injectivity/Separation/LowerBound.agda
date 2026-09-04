module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.LowerBound where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ; addIdR)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Bounds
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.SinePositive
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.CosineFactor
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.PositiveProduct
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Geometry
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Phase
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Factors


open PositiveRationals using (ℚ₊)


quarterTurnSineSeparationFloor : ℚ₊ → ℝ
quarterTurnSineSeparationFloor probe = sinℝ (rat (fst probe))


quarterTurnSineSeparationBound : ℚ₊ → ℝ
quarterTurnSineSeparationBound probe =
  let floor = quarterTurnSineSeparationFloor probe
  in (floor · floor) + (floor · floor)


opaque
  quarterTurnSineSeparationBound-positive : ∀ (probe : ℚ₊) →
    0ℝ <ℝ quarterTurnSineSeparationFloor probe →
    0ℝ <ℝ quarterTurnSineSeparationBound probe
  quarterTurnSineSeparationBound-positive probe floor-positive =
    positiveProductTwice
      (quarterTurnSineSeparationFloor probe)
      (quarterTurnSineSeparationFloor probe)
      floor-positive floor-positive


  quarterTurnSineDifference-lowerBound : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ (probe : ℚ₊) x y →
    (- quarter) ≤ℝ x → y ≤ℝ quarter → x <ℝ y →
    rat (fst probe) <ℝ quarterTurnHalfDifference x y →
    quarterTurnSineSeparationBound probe
      <ℝ sinℝ y + (- sinℝ x)
  quarterTurnSineDifference-lowerBound
      quarter positive-quarter characterization probe x y
      negative-quarter≤x y≤quarter x<y probe<difference =
    subst
      (quarterTurnSineSeparationBound probe <ℝ_)
      (sym (sinℝ-quarterTurnDifference x y))
      (<ℝ-add
        (floor · floor) product
        (floor · floor) product
        floor-square<product floor-square<product)
    where
    floor : ℝ
    floor = quarterTurnSineSeparationFloor probe

    product : ℝ
    product =
      cosℝ (quarterTurnMidpoint x y)
        · sinℝ (quarterTurnHalfDifference x y)

    floor-square<product : floor · floor <ℝ product
    floor-square<product =
      quarterTurnSeparationFloorSquare<product
        quarter positive-quarter characterization probe x y
        negative-quarter≤x y≤quarter x<y probe<difference

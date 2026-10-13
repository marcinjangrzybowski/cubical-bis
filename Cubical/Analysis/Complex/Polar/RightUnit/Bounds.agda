module Cubical.Analysis.Complex.Polar.RightUnit.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Continuity
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.SquareRoot.Order
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base

module RightUnitBounds (a b : ℝ) (positive : 0ℝ <ℝ a) (unit : a · a + b · b ≡ 1ℝ) where
  opaque
    b-square-small : b · b <ℝ 1ℝ
    b-square-small = subst2 _<ℝ_ (addIdL (b · b)) unit
      (<ℝ-addR 0ℝ (a · a) (b · b) (mulPositive a a positive positive))

    abs-b-small : absℝ b <ℝ 1ℝ
    abs-b-small = continuousReflectsStrictOnOrderedInputs squareℝ square-isContinuous
      (absℝ b) 1ℝ
      (squareReflects≤Nonnegative (absℝ b) 1ℝ (isNonnegative→0≤ 1ℝ oneIsNonnegative)
        (<ℝ-weaken (absℝ b · absℝ b) (1ℝ · 1ℝ) squares)) squares
      where
      squares : absℝ b · absℝ b <ℝ 1ℝ · 1ℝ
      squares = subst2 _<ℝ_ (sym (absSquared b)) (sym (mulIdR 1ℝ)) b-square-small

    b-above : (- 1ℝ) <ℝ b
    b-above = subst ((- 1ℝ) <ℝ_) (negInvol b)
      (<ℝ-neg (- b) 1ℝ (≤<ℝ-trans (- b) (absℝ b) 1ℝ (negLeAbs b) abs-b-small))

    b-below : b <ℝ 1ℝ
    b-below = ≤<ℝ-trans b (absℝ b) 1ℝ (leAbs b) abs-b-small

    sinePoint : SineUnitInterval
    sinePoint = symmetricIntervalFromAbsBound 1ℝ b (<ℝ-weaken (absℝ b) 1ℝ abs-b-small)

    sinePoint-value : fst sinePoint ≡ b
    sinePoint-value = refl

module Cubical.Analysis.Complex.Polar.RightUnit.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
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
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pythagorean
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseValue
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseValue.Properties
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Polar.Cis

private
  module R = RingTheory (CommRing→Ring ℝCommRing)

open import Cubical.Analysis.Complex.Polar.RightUnit.Bounds

private
  opaque
    composeImagePath : (f : ℝ → ℝ) (x y z w : ℝ) →
      x ≡ y → f y ≡ z → z ≡ w → f x ≡ w
    composeImagePath f x y z w p q r = cong f p ∙ q ∙ r

    moveStrict : ∀ x x′ y y′ → x ≡ x′ → y ≡ y′ → x <ℝ y → x′ <ℝ y′
    moveStrict x x′ y y′ p q = subst2 _<ℝ_ p q

module RightUnitInverse (a b : ℝ) (positive : 0ℝ <ℝ a) (unit : a · a + b · b ≡ 1ℝ) where
  open RightUnitBounds a b positive unit

  opaque
    argument : ℝ
    argument = fst (arcSinℝ sinePoint)

    argument-value : argument ≡ fst (arcSinℝ sinePoint)
    argument-value = refl

  opaque
    sine-argument : sinℝ argument ≡ b
    sine-argument = composeImagePath sinℝ argument (fst (arcSinℝ sinePoint))
      (fst sinePoint) b argument-value (sinℝ-arcSinℝ sinePoint) sinePoint-value

    argument-above : (- halfPiℝ) <ℝ argument
    argument-above = moveStrict (fst (arcSinℝ sineUnitLeft)) (- halfPiℝ)
      (fst (arcSinℝ sinePoint)) argument arcSinℝ-left (sym argument-value)
      (arcSinℝ-strictlyIncreasing sineUnitLeft sinePoint
        (moveStrict (- 1ℝ) (- 1ℝ) b (fst sinePoint) refl (sym sinePoint-value) b-above))

    argument-below : argument <ℝ halfPiℝ
    argument-below = moveStrict (fst (arcSinℝ sinePoint)) argument
      (fst (arcSinℝ sineUnitRight)) halfPiℝ (sym argument-value) arcSinℝ-right
      (arcSinℝ-strictlyIncreasing sinePoint sineUnitRight
        (moveStrict b (fst sinePoint) 1ℝ 1ℝ (sym sinePoint-value) refl b-below))

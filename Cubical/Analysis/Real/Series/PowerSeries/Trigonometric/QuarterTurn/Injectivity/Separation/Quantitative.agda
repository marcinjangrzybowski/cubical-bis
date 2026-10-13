module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Quantitative where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ using (ℚ)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Points
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.LowerBound
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Modulus
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Build
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Radius

open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.SmallAngle

open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Quantitative.Algebra using (squareRadius; halfRadius)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Quantitative.Bounds

-- This modulus is computed by rational arithmetic. It does not select a
-- family from the earlier radiuswise truncated separation theorem.
opaque
  sineSeparationProbe : ℚ₊ → ℚ₊
  sineSeparationProbe input = min₊ 1 input /2₊

  sineSeparationProbe≤one : ∀ input → rat (fst (sineSeparationProbe input)) ≤ℝ 1ℝ
  sineSeparationProbe≤one input =
    <ℝ-weaken (rat (fst (sineSeparationProbe input))) 1ℝ
      (<ℚ→<ℝ (fst (sineSeparationProbe input)) 1 (min/2₊<L 1 input))

  sineSeparationProbe<input : ∀ input →
    rat (fst (sineSeparationProbe input)) <ℝ rat (fst input)
  sineSeparationProbe<input input =
    <ℚ→<ℝ (fst (sineSeparationProbe input)) (fst input) (min/2₊<R 1 input)

sineSeparationOutput : ℚ₊ → ℚ₊
sineSeparationOutput input =
  squareRadius (halfRadius (sineSeparationProbe input))


private
  opaque
    output≤separationBound : ∀ input →
      rat (fst (sineSeparationOutput input)) ≤ℝ
        quarterTurnSineSeparationBound (sineSeparationProbe input)
    output≤separationBound input = rationalHalfSquareBound (sineSeparationProbe input)
      (sineSeparationProbe≤one input)

opaque
  characterizedQuarterTurn-explicitOrderedSeparation : ∀ quarter →
    IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
    ∀ input → QuarterTurnOrderedSineSeparation quarter input (sineSeparationOutput input)
  characterizedQuarterTurn-explicitOrderedSeparation quarter turn first input x y left right gap =
    ≤<ℝ-trans (rat (fst (sineSeparationOutput input)))
      (quarterTurnSineSeparationBound (sineSeparationProbe input)) (sinℝ y + (- sinℝ x))
      (output≤separationBound input)
      (quarterTurnSineDifference-lowerBound quarter turn first (sineSeparationProbe input) x y left right
        (positiveSub→< x y (<≤ℝ-trans 0ℝ
          (rat (fst input) + rat (fst input)) (y - x)
          (snd (positiveRat input +>0 positiveRat input)) gap))
        (<≤ℝ-trans (rat (fst (sineSeparationProbe input))) (rat (fst input)) (quarterTurnHalfDifference x y)
          (sineSeparationProbe<input input)
          (subst (λ z → z ≤ℝ quarterTurnHalfDifference x y)
            (quarterTurnHalfScalar-double (rat (fst input)))
            (quarterTurnHalfScalar-pres≤
              {x = rat (fst input) + rat (fst input)} {y = y - x} gap))))

characterizedQuarterTurn-chosenSineClosenessReflectionModulus : ∀ quarter →
  IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
  ChosenQuarterTurnSineClosenessReflectionModulus quarter
characterizedQuarterTurn-chosenSineClosenessReflectionModulus quarter turn first input =
  sineSeparationOutput (input /4₊) ,
  orderedSineSeparationBelowRadius→closenessReflection quarter (input /4₊) input
    (sineSeparationOutput (input /4₊)) (quarterRadiusDouble<radius input)
    (characterizedQuarterTurn-explicitOrderedSeparation quarter turn first (input /4₊))

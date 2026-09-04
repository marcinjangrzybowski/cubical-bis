module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Modulus where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ; addIdL)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Positive using (gapLowerBound)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.PositiveProduct
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Points
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Factors
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.LowerBound


open PositiveRationals using
  (ℚ₊; min₊; min/2₊<L; min/2₊<R)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)


QuarterTurnOrderedSineSeparation : ℝ → ℚ₊ → ℚ₊ → Type₀
QuarterTurnOrderedSineSeparation quarter input output =
  ∀ x y →
  (- quarter) ≤ℝ x → y ≤ℝ quarter →
  rat (fst input) + rat (fst input) ≤ℝ (y - x) →
  rat (fst output) <ℝ sinℝ y + (- sinℝ x)


QuarterTurnOrderedSineSeparationModulus : ℝ → Type₀
QuarterTurnOrderedSineSeparationModulus quarter =
  ∀ input →
  ∥ Σ[ output ∈ ℚ₊ ]
      QuarterTurnOrderedSineSeparation quarter input output ∥₁


opaque
  characterizedQuarterTurn-orderedSineSeparationModulus : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    QuarterTurnOrderedSineSeparationModulus quarter
  characterizedQuarterTurn-orderedSineSeparationModulus
      quarter positive-quarter characterization input =
    PT.rec squash₁ build-from-quarter-gap zero<quarter
    where
    zero<quarter : 0ℝ <ℝ quarter
    zero<quarter = firstPositiveCosineZero-positive characterization

    build-from-quarter-gap : PositiveGap 0ℝ quarter →
      ∥ Σ[ output ∈ ℚ₊ ]
          QuarterTurnOrderedSineSeparation quarter input output ∥₁
    build-from-quarter-gap (quarter-width , quarter-bound) =
      PT.map build-from-output-gap separation-bound-positive
      where
      probe : ℚ₊
      probe = min₊ quarter-width input /2₊

      probe<quarter-width : fst probe ℚOrder.< fst quarter-width
      probe<quarter-width = min/2₊<L quarter-width input

      probe<input : fst probe ℚOrder.< fst input
      probe<input = min/2₊<R quarter-width input

      quarter-width≤quarter : rat (fst quarter-width) ≤ℝ quarter
      quarter-width≤quarter =
        gapLowerBound (quarter-width , quarter-bound)

      probe≤quarter : rat (fst probe) ≤ℝ quarter
      probe≤quarter =
        ≤ℝ-trans
          (rat (fst probe)) (rat (fst quarter-width)) quarter
          (<ℝ-weaken (rat (fst probe)) (rat (fst quarter-width))
            (<ℚ→<ℝ (fst probe) (fst quarter-width)
              probe<quarter-width))
          quarter-width≤quarter

      floor-positive :
        0ℝ <ℝ quarterTurnSineSeparationFloor probe
      floor-positive =
        quarterTurnSeparationFloor-positive
          quarter positive-quarter characterization probe probe≤quarter

      separation-bound-positive :
        0ℝ <ℝ quarterTurnSineSeparationBound probe
      separation-bound-positive =
        quarterTurnSineSeparationBound-positive probe floor-positive

      build-from-output-gap :
        PositiveGap 0ℝ (quarterTurnSineSeparationBound probe) →
        Σ[ output ∈ ℚ₊ ]
          QuarterTurnOrderedSineSeparation quarter input output
      build-from-output-gap (output , output-bound) =
        output , separate
        where
        output≤separation-bound :
          rat (fst output) ≤ℝ quarterTurnSineSeparationBound probe
        output≤separation-bound =
          gapLowerBound (output , output-bound)

        separate : QuarterTurnOrderedSineSeparation quarter input output
        separate x y negative-quarter≤x y≤quarter input-double≤difference =
          ≤<ℝ-trans
            (rat (fst output))
            (quarterTurnSineSeparationBound probe)
            (sinℝ y + (- sinℝ x))
            output≤separation-bound
            (quarterTurnSineDifference-lowerBound
              quarter positive-quarter characterization probe x y
              negative-quarter≤x y≤quarter x<y probe<half-difference)
          where
          zero<input : 0ℝ <ℝ rat (fst input)
          zero<input = positiveRational-real-positive input

          zero<input-double :
            0ℝ <ℝ rat (fst input) + rat (fst input)
          zero<input-double =
            snd (positiveRat input +>0 positiveRat input)

          zero<difference : 0ℝ <ℝ y - x
          zero<difference =
            <≤ℝ-trans
              0ℝ (rat (fst input) + rat (fst input)) (y - x)
              zero<input-double input-double≤difference

          x<y : x <ℝ y
          x<y = positiveSub→< x y zero<difference

          input≤half-difference :
            rat (fst input) ≤ℝ quarterTurnHalfDifference x y
          input≤half-difference =
            subst (λ z → z ≤ℝ quarterTurnHalfDifference x y)
              (quarterTurnHalfScalar-double (rat (fst input)))
              (quarterTurnHalfScalar-pres≤
                {x = rat (fst input) + rat (fst input)}
                {y = y - x}
                input-double≤difference)

          probe<input-real : rat (fst probe) <ℝ rat (fst input)
          probe<input-real =
            <ℚ→<ℝ (fst probe) (fst input) probe<input

          probe<half-difference :
            rat (fst probe) <ℝ quarterTurnHalfDifference x y
          probe<half-difference =
            <≤ℝ-trans
              (rat (fst probe)) (rat (fst input))
              (quarterTurnHalfDifference x y)
              probe<input-real input≤half-difference

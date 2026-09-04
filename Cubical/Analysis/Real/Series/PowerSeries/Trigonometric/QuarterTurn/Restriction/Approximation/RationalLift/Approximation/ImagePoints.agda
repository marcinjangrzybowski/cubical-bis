module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.ImagePoints where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Choice
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Sequence.Mere
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.Base


-- An approximate evaluator only has to keep its rational source points in
-- the quarter interval and make their sine images converge.  Under the
-- explicit choice hypothesis, convergence supplies an image `SeqWitness`;
-- the selected inverse modulus then reflects it back to the source points.

RationalPointSineInverseImageApproximation : ℝ → ℚ → Type₀
RationalPointSineInverseImageApproximation quarter q =
  Σ[ points ∈ (ℕ → ℚ) ]
    (∀ n →
      ((- quarter) ≤ℝ rat (points n)) ×
      (rat (points n) ≤ℝ quarter))
    × isLimitSequence
        (λ n → sinℝ (rat (points n)))
        (unitClamp (rat q))


RationalPointSineInverseImageApproximationFamily : ℝ → Type₀
RationalPointSineInverseImageApproximationFamily quarter =
  (q : ℚ) → RationalPointSineInverseImageApproximation quarter q


rationalPointSineInverseImageApproximation→approximation :
  ∀ quarter q →
  PositiveRationalChoice₀ →
  MereChosenQuarterTurnSineClosenessReflectionModulus quarter →
  RationalPointSineInverseImageApproximation quarter q →
  RationalSineInverseApproximation quarter q
rationalPointSineInverseImageApproximation→approximation
    quarter q choice modulus (points , bounds , image-limit) =
  (λ n → rat (points n) , bounds n)
  , mereChosenSineClosenessReflection-presSeqWitness
      quarter modulus
      (λ n → rat (points n) , bounds n)
      (positiveRationalChoice→convergentSeqWitness choice image-limit)
  , image-limit


rationalPointSineInverseImageApproximationFamily→approximationFamily :
  ∀ quarter →
  PositiveRationalChoice₀ →
  MereChosenQuarterTurnSineClosenessReflectionModulus quarter →
  RationalPointSineInverseImageApproximationFamily quarter →
  RationalSineInverseApproximationFamily quarter
rationalPointSineInverseImageApproximationFamily→approximationFamily
    quarter choice modulus approximations q =
  rationalPointSineInverseImageApproximation→approximation
    quarter q choice modulus (approximations q)

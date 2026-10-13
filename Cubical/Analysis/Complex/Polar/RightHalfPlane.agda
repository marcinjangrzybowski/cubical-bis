module Cubical.Analysis.Complex.Polar.RightHalfPlane where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.NormSquared
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Polar.RightUnit
open import Cubical.Analysis.Complex.Polar.RightUnit.Bounds
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseValue using (arcSinℝ)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base using (SineUnitInterval)
import Cubical.Analysis.Complex.Polar.Algebra as AlgebraDefinition

private
  module A = AlgebraDefinition.PolarAlgebra ℝCommRing

module RightHalfPlane (z : ℂ) (positive-real-part : 0ℝ <ℝ re z) where
  modulus-positive : 0ℝ <ℝ modulusℂ z
  modulus-positive = <≤ℝ-trans 0ℝ (re z) (modulusℂ z) positive-real-part
    (≤ℝ-trans (re z) (absℝ (re z)) (modulusℂ z) (leAbs (re z)) (reAbs≤modulusℂ z))

  private
    reciprocal : ℝ
    reciprocal = positiveReciprocal (modulusℂ z) modulus-positive

    inverse : modulusℂ z · reciprocal ≡ 1ℝ
    inverse = positiveReciprocalLaw (modulusℂ z) modulus-positive

    normalized-positive : 0ℝ <ℝ re z · reciprocal
    normalized-positive = mulPositive (re z) reciprocal positive-real-part
      (positiveReciprocalPositive (modulusℂ z) modulus-positive)

    normalized-unit : (re z · reciprocal) · (re z · reciprocal) +
      (im z · reciprocal) · (im z · reciprocal) ≡ 1ℝ
    normalized-unit = A.normalizedSquare (re z) (im z) (modulusℂ z) reciprocal
      (modulusℂ-square z) inverse

    module B = RightUnitBounds (re z · reciprocal) (im z · reciprocal) normalized-positive normalized-unit
    module U = RightUnit (re z · reciprocal) (im z · reciprocal) normalized-positive normalized-unit

  opaque
    argument : ℝ
    argument = U.argument

    -- Expose the existing normalized arcsine construction by value laws.
    -- Continuity proofs can now reuse it without unfolding its completion.
    normalizedImaginary : SineUnitInterval
    normalizedImaginary = B.sinePoint

    normalizedImaginary-value : fst normalizedImaginary ≡ im z · positiveReciprocal (modulusℂ z) modulus-positive
    normalizedImaginary-value = B.sinePoint-value

    argument-asArcSin : argument ≡ fst (arcSinℝ normalizedImaginary)
    argument-asArcSin = U.argument-value

    reconstruct : polarℂ (modulusℂ z) argument ≡ z
    reconstruct = cong (fromℝ (modulusℂ z) ·ℂ_) U.reconstruct
      ∙ A.undoScale (modulusℂ z) reciprocal (re z) (im z) inverse

module Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Data.Sigma
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Order.AbsoluteValue using (absOfNonnegative)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Functions.Logarithm.Global
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Values using (sineUnitZero)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseValue using (arcSinℝ)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseValue.Properties using (arcSinℝ-zero)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Domain.RightHalfPlane
import Cubical.Analysis.Complex.Polar.RightHalfPlane as Polar
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Base

private module R = RingTheory (CommRing→Ring ℝCommRing)

positiveRealInRightHalfPlane : ℝ>0 → ComplexRightHalfPlane
positiveRealInRightHalfPlane (x , positive) = fromℝ x , positive

opaque
  rightHalfPlaneArgument-real : ∀ (x : ℝ>0) → rightHalfPlaneArgument (positiveRealInRightHalfPlane x) ≡ 0ℝ
  rightHalfPlaneArgument-real (x , positive) = P.argument-asArcSin
    ∙ cong (λ t → fst (arcSinℝ t)) (sineUnitInterval≡ P.normalizedImaginary sineUnitZero
      (P.normalizedImaginary-value ∙ R.0LeftAnnihilates (positiveReciprocal (modulusℂ (fromℝ x)) P.modulus-positive)))
    ∙ arcSinℝ-zero
    where module P = Polar.RightHalfPlane (fromℝ x) positive

opaque
  rightHalfPlaneRadius-real : ∀ (x : ℝ>0) → rightHalfPlaneRadius (positiveRealInRightHalfPlane x) ≡ x
  rightHalfPlaneRadius-real (x , positive) = Σ≡Prop (isProp<ℝ 0ℝ)
    (modulusℂ-fromℝ x ∙ absOfNonnegative x (<ℝ-weaken 0ℝ x positive))

-- The branch agrees with the existing real logarithm on the positive axis.
opaque
  rightHalfPlaneLog-real : ∀ (x : ℝ>0) → rightHalfPlaneLog (positiveRealInRightHalfPlane x) ≡ fromℝ (logℝ x)
  rightHalfPlaneLog-real x = rightHalfPlaneLog-value (positiveRealInRightHalfPlane x)
    ∙ ℂ≡ (cong logℝ (rightHalfPlaneRadius-real x)) (rightHalfPlaneArgument-real x)

-- Normalize at a positive-real domain point whose value is one. Keeping
-- the point abstract avoids reducing its native completion representation.
opaque
  rightHalfPlaneLog-atOne : (x : ℝ>0) → fst x ≡ 1ℝ → rightHalfPlaneLog (positiveRealInRightHalfPlane x) ≡ 0ℂ
  rightHalfPlaneLog-atOne x one = rightHalfPlaneLog-real x ∙ cong fromℝ (logℝ-atOne x one)

opaque
  rightHalfPlaneLog-injective : ∀ (p q : ComplexRightHalfPlane) → rightHalfPlaneLog p ≡ rightHalfPlaneLog q → p ≡ q
  rightHalfPlaneLog-injective p q equal = Σ≡Prop (λ z → isProp<ℝ 0ℝ (re z)) {u = p} {v = q}
    (sym (expℂ-rightHalfPlaneLog p) ∙ cong expℂ equal ∙ expℂ-rightHalfPlaneLog q)

module Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Algebra.Inverse.Continuity
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (leAbs; absOfNonnegative)
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Strict.Slack using (positiveSlack)
open import Cubical.Analysis.Real.Functions.Logarithm.Global
open import Cubical.Analysis.Real.Functions.Logarithm.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseValue.Properties
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.UniformDerivative.Continuity
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Modulus.Continuity
open import Cubical.Analysis.Complex.Domain.RightHalfPlane
import Cubical.Analysis.Complex.Polar.RightHalfPlane as Polar
open import Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Base

module _ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
  (point : A → ComplexRightHalfPlane) (η : ℚ₊) (radius : ℝ)
  (lower : ∀ x → rat (fst η) ≤ℝ re (fst (point x)))
  (bounded : ∀ x → normℂ (fst (point x)) ≤ℝ radius)
  (continuous : IsRadiuswiseUniformlyContinuous source (fst ∘ point) (ℂPremetricSpace .snd)) where
  private
    modulus : A → ℝ
    modulus x = modulusℂ (fst (point x))
    reciprocal : A → ℝ
    reciprocal x = positiveReciprocal (modulus x) (snd (rightHalfPlaneRadius (point x)))
    reciprocalBound : ℝ
    reciprocalBound = positiveReciprocal (rat (fst η)) (positiveSlack η)

    modulusLower : ∀ x → rat (fst η) ≤ℝ modulus x
    modulusLower x = ≤ℝ-trans (rat (fst η)) (re (fst (point x))) (modulus x) (lower x)
      (≤ℝ-trans (re (fst (point x))) (absℝ (re (fst (point x)))) (modulus x)
        (leAbs (re (fst (point x)))) (reAbs≤modulusℂ (fst (point x))))

    modulusUniform : IsRadiuswiseUniformlyContinuous source modulus (ℝPremetricSpace .snd)
    modulusUniform ε = do
      (δ , near) ← continuous (ε /2₊)
      return (δ , λ x y close → modulusℂ-presCloseness (fst (point x)) (fst (point y)) ε (near x y close))

    reciprocalUniform : IsRadiuswiseUniformlyContinuous source reciprocal (ℝPremetricSpace .snd)
    reciprocalUniform = positiveReciprocalUniformAlong source modulus
      (λ x → snd (rightHalfPlaneRadius (point x))) η modulusLower modulusUniform

    reciprocalAbsBound : ∀ x → absℝ (reciprocal x) ≤ℝ reciprocalBound
    reciprocalAbsBound x = subst (_≤ℝ reciprocalBound)
      (sym (absOfNonnegative (reciprocal x) (<ℝ-weaken 0ℝ (reciprocal x)
        (positiveReciprocalPositive (modulus x) (snd (rightHalfPlaneRadius (point x)))))))
      (positiveReciprocalReverses≤ (rat (fst η)) (modulus x) (positiveSlack η)
        (snd (rightHalfPlaneRadius (point x))) (modulusLower x))

    normalizedUniform : IsRadiuswiseUniformlyContinuous source
      (λ x → im (fst (point x)) · reciprocal x) (ℝPremetricSpace .snd)
    normalizedUniform = boundedProductIsRadiuswiseUniformlyContinuous source
      (im ∘ fst ∘ point) reciprocal radius reciprocalBound
      (λ x → ≤ℝ-trans (absℝ (im (fst (point x)))) (normℂ (fst (point x))) radius
        (imAbs≤normℂ (fst (point x))) (bounded x)) reciprocalAbsBound
      (λ ε → do
        (δ , near) ← continuous ε
        return (δ , λ x y close → snd (near x y close))) reciprocalUniform

  rightHalfPlaneArgumentUniformAlong : IsRadiuswiseUniformlyContinuous source
    (rightHalfPlaneArgument ∘ point) (ℝPremetricSpace .snd)
  rightHalfPlaneArgumentUniformAlong ε = do
    (δ , near) ← normalizedUniform (inverseTrigRadius ε)
    return (δ , λ x y close → subst2 (_∼[ ε ]_)
      (sym (Polar.RightHalfPlane.argument-asArcSin (fst (point x)) (snd (point x))))
      (sym (Polar.RightHalfPlane.argument-asArcSin (fst (point y)) (snd (point y))))
      (arcSinℝ-pres∼ ε
        (Polar.RightHalfPlane.normalizedImaginary (fst (point x)) (snd (point x)))
        (Polar.RightHalfPlane.normalizedImaginary (fst (point y)) (snd (point y)))
        (subst2 (_∼[ inverseTrigRadius ε ]_)
          (sym (Polar.RightHalfPlane.normalizedImaginary-value (fst (point x)) (snd (point x))))
          (sym (Polar.RightHalfPlane.normalizedImaginary-value (fst (point y)) (snd (point y))))
          (near x y close))))

  -- The branch is uniformly continuous on each bounded region separated
  -- from the imaginary axis. The radii remain separately truncated.
  rightHalfPlaneLogUniformAlong : IsRadiuswiseUniformlyContinuous source
    (rightHalfPlaneLog ∘ point) (ℂPremetricSpace .snd)
  rightHalfPlaneLogUniformAlong ε = do
    (δ , realNear) ← logℝUniformAlongAbove source (rightHalfPlaneRadius ∘ point)
      (rat (fst η) , positiveSlack η) modulusLower modulusUniform ε
    (ρ , imaginaryNear) ← rightHalfPlaneArgumentUniformAlong ε
    return (min₊ δ ρ , λ x y close → subst2 (_∼ℂ[ ε ]_)
      (sym (rightHalfPlaneLog-value (point x))) (sym (rightHalfPlaneLog-value (point y)))
      (realNear x y (PremetricStr.isMonotone≈≤ source x y (min₊ δ ρ) δ (min₊≤L δ ρ) close) ,
       imaginaryNear x y (PremetricStr.isMonotone≈≤ source x y (min₊ δ ρ) ρ (min₊≤R δ ρ) close)))

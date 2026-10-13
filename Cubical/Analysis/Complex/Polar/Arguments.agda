module Cubical.Analysis.Complex.Polar.Arguments where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum as Sum
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Polar.CoordinateCases
open import Cubical.Analysis.Complex.Polar.RightHalfPlane
open import Cubical.Analysis.Complex.Polar.Rotations
import Cubical.Analysis.Complex.Polar.Algebra as AlgebraDefinition

private
  module A = AlgebraDefinition.PolarAlgebra ℝCommRing

PolarWitness : ℂ → Type₀
PolarWitness z = Σ[ θ ∈ ℝ ] polarℂ (modulusℂ z) θ ≡ z

rightPolarWitness : ∀ z → 0ℝ <ℝ re z → PolarWitness z
rightPolarWitness z positive = RightHalfPlane.argument z positive , RightHalfPlane.reconstruct z positive

private
  negateWitness : ∀ z → PolarWitness (-ℂ z) → PolarWitness z
  negateWitness z (θ , reconstruct) = (θ + piℝ) ,
    cong (λ r → polarℂ r (θ + piℝ)) (sym (modulusℂ-neg z))
      ∙ polarℂ-add-pi (modulusℂ (-ℂ z)) θ
      ∙ cong -ℂ_ reconstruct ∙ ℂRing.-Idempotent z

leftPolarWitness : ∀ z → 0ℝ <ℝ (- re z) → PolarWitness z
leftPolarWitness z positive = negateWitness z (rightPolarWitness (-ℂ z) positive)

upperPolarWitness : ∀ z → 0ℝ <ℝ im z → PolarWitness z
upperPolarWitness z positive = (θ + halfPiℝ) ,
  cong (λ r → polarℂ r (θ + halfPiℝ)) (sym same-modulus)
    ∙ polarℂ-add-halfPi (modulusℂ rotated) θ
    ∙ cong (iℂ ·ℂ_) (snd witness) ∙ A.undoQuarterRotate (re z) (im z)
  where
  rotated : ℂ
  rotated = im z , - re z

  same-modulus : modulusℂ rotated ≡ modulusℂ z
  same-modulus = cong modulusℂ (sym (A.negativeQuarterRotate (re z) (im z)))
    ∙ modulusℂ-negativeQuarterRotate z

  witness : PolarWitness rotated
  witness = rightPolarWitness rotated positive

  θ : ℝ
  θ = fst witness

lowerPolarWitness : ∀ z → 0ℝ <ℝ (- im z) → PolarWitness z
lowerPolarWitness z positive = negateWitness z (upperPolarWitness (-ℂ z) positive)

-- Arguments exist locally away from zero. Only a finite truncated witness
-- is returned; there is no globally selected branch of the argument.
nonzeroPolarWitness : ∀ z → 0ℝ <ℝ modulusℂ z → ∥ PolarWitness z ∥₁
nonzeroPolarWitness z positive = PT.map
  (Sum.rec (rightPolarWitness z)
    (Sum.rec (leftPolarWitness z) (Sum.rec (upperPolarWitness z) (lowerPolarWitness z))))
  (nonzeroCoordinateCases z positive)

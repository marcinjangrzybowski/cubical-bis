module Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Continuity
open import Cubical.Analysis.Real.Domain.OpenInterval
open import Cubical.Analysis.Real.Functions.Logarithm.Global
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseValue
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Continuity
open import Cubical.Analysis.Complex.Domain.RightHalfPlane
import Cubical.Analysis.Complex.Polar.RightHalfPlane as Polar
open import Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Base

private
  H = RightHalfPlanePremetricSpace .snd
  reciprocalRadius : ComplexRightHalfPlane → ℝ
  reciprocalRadius p = positiveReciprocal (modulusℂ (fst p)) (snd (rightHalfPlaneRadius p))

rightHalfPlaneRadiusIsContinuous : isContinuous H rightHalfPlaneRadius (LowerOpenHalfLinePremetricSpace 0ℝ .snd)
rightHalfPlaneRadiusIsContinuous x .IsContinuousAt.pres≈ ε = do
  (δ , near) ← modulusℂ-isContinuous (fst x) .IsContinuousAt.pres≈ ε
  return (δ , λ y close → near (fst y) close)

private
  normalizedIsContinuous : isContinuous H
    (λ p → im (fst p) · reciprocalRadius p) (ℝPremetricSpace .snd)
  normalizedIsContinuous = mulOfContinuousIsContinuous H (im ∘ fst) reciprocalRadius
    (snd ((im , imℂ-isContinuous) ∘C NE→C rightHalfPlaneInclusionNE))
    (snd (((λ x → positiveReciprocal (fst x) (snd x)) , positiveReciprocalIsContinuous) ∘C
      (rightHalfPlaneRadius , rightHalfPlaneRadiusIsContinuous)))

rightHalfPlaneArgumentIsContinuous : isContinuous H rightHalfPlaneArgument (ℝPremetricSpace .snd)
rightHalfPlaneArgumentIsContinuous x .IsContinuousAt.pres≈ ε = do
  (ρ , arcsineNear) ← arcSinℝ-isContinuous (Polar.RightHalfPlane.normalizedImaginary (fst x) (snd x)) .IsContinuousAt.pres≈ ε
  (δ , normalizedNear) ← normalizedIsContinuous x .IsContinuousAt.pres≈ ρ
  return (δ , λ y close → subst2 (_∼[ ε ]_)
    (sym (Polar.RightHalfPlane.argument-asArcSin (fst x) (snd x)))
    (sym (Polar.RightHalfPlane.argument-asArcSin (fst y) (snd y)))
    (arcsineNear (Polar.RightHalfPlane.normalizedImaginary (fst y) (snd y))
      (subst2 (_∼[ ρ ]_)
        (sym (Polar.RightHalfPlane.normalizedImaginary-value (fst x) (snd x)))
        (sym (Polar.RightHalfPlane.normalizedImaginary-value (fst y) (snd y)))
        (normalizedNear y close))))

rightHalfPlaneLogIsContinuous : isContinuous H rightHalfPlaneLog (ℂPremetricSpace .snd)
rightHalfPlaneLogIsContinuous = subst (λ f → isContinuous H f (ℂPremetricSpace .snd))
  (sym (funExt rightHalfPlaneLog-value))
  (pairℂ-isContinuous H (logℝ ∘ rightHalfPlaneRadius) rightHalfPlaneArgument
    (snd ((logℝ , logℝ-isContinuous) ∘C (rightHalfPlaneRadius , rightHalfPlaneRadiusIsContinuous)))
    rightHalfPlaneArgumentIsContinuous)

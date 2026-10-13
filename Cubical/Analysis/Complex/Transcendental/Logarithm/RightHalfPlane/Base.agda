module Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Positive using (ℝ>0)
open import Cubical.Analysis.Real.Functions.Logarithm.Global
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Inverse
open import Cubical.Analysis.Complex.Inverse.Bounds
open import Cubical.Analysis.Complex.Domain.RightHalfPlane
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Polar.Arguments using (PolarWitness; rightPolarWitness)
import Cubical.Analysis.Complex.Polar.RightHalfPlane as Polar
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Logarithm.Base

rightHalfPlaneRadius : ComplexRightHalfPlane → ℝ>0
rightHalfPlaneRadius (z , positive) = modulusℂ z , Polar.RightHalfPlane.modulus-positive z positive

rightHalfPlaneArgument : ComplexRightHalfPlane → ℝ
rightHalfPlaneArgument (z , positive) = Polar.RightHalfPlane.argument z positive

private
  polarWitness : ∀ (p : ComplexRightHalfPlane) → PolarWitness (fst p)
  polarWitness (z , positive) = rightPolarWitness z positive

-- This is an actual branch on an intrinsic open domain. It reuses the
-- previously constructed restricted arcsine, positive real logarithm and
-- polar reconstruction, with no chosen argument for the punctured plane.
rightHalfPlaneLog : ComplexRightHalfPlane → ℂ
rightHalfPlaneLog p = fst (logarithmFromPolar (fst p) (snd (rightHalfPlaneRadius p)) (polarWitness p))

rightHalfPlaneLog-value : ∀ (p : ComplexRightHalfPlane) → rightHalfPlaneLog p ≡ (logℝ (rightHalfPlaneRadius p) , rightHalfPlaneArgument p)
rightHalfPlaneLog-value p = logarithmFromPolar-value (fst p) (snd (rightHalfPlaneRadius p)) (polarWitness p)

expℂ-rightHalfPlaneLog : ∀ (p : ComplexRightHalfPlane) → expℂ (rightHalfPlaneLog p) ≡ fst p
expℂ-rightHalfPlaneLog p = snd (logarithmFromPolar (fst p) (snd (rightHalfPlaneRadius p)) (polarWitness p))

rightHalfPlaneNonzero : ∀ (p : ComplexRightHalfPlane) → ComplexNonzero (fst p)
rightHalfPlaneNonzero p = modulusPositive→nonzeroℂ (fst p) (snd (rightHalfPlaneRadius p))

rightHalfPlaneReciprocal : ComplexRightHalfPlane → ℂ
rightHalfPlaneReciprocal p = inverseℂ (fst p) (rightHalfPlaneNonzero p)

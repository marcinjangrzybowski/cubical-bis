module Cubical.Analysis.Complex.Transcendental.Logarithm.Base where

-- The generic logarithm constructor uses a supplied polar witness.
-- Unrestricted existence stays truncated; no global argument is selected.
open import Cubical.Foundations.Prelude
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Positive using (ℝ>0)
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Functions.Logarithm.Global
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Inverse
open import Cubical.Analysis.Complex.Inverse.Bounds
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Polar.Arguments
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Properties

ComplexLogarithmWitness : ℂ → Type₀
ComplexLogarithmWitness z = Σ[ w ∈ ℂ ] expℂ w ≡ z


opaque
  logarithmFromPolar : ∀ z → 0ℝ <ℝ modulusℂ z → PolarWitness z → ComplexLogarithmWitness z
  logarithmFromPolar z positive (θ , reconstruct) = (logℝ radius , θ) ,
    (expℂ-positivePolar (logℝ radius) θ
      ∙ cong (λ r → polarℂ (fst r) θ) (expPositive-logℝ radius) ∙ reconstruct)
    where
    radius : ℝ>0
    radius = modulusℂ z , positive

  logarithmFromPolar-value : ∀ z positive polar →
    fst (logarithmFromPolar z positive polar) ≡ (logℝ (modulusℂ z , positive) , fst polar)
  logarithmFromPolar-value z positive polar = refl

  complexLogarithmExists : ∀ z → ComplexNonzero z → PT.∥ ComplexLogarithmWitness z ∥₁
  complexLogarithmExists z nonzero = PT.map (logarithmFromPolar z positive)
    (nonzeroPolarWitness z positive)
    where
    positive : 0ℝ <ℝ modulusℂ z
    positive = unit→modulusPositiveℂ z (inverseℂ z nonzero) (inverseℂ-law z nonzero)

  complexLogarithm→nonzero : ∀ z → PT.∥ ComplexLogarithmWitness z ∥₁ → ComplexNonzero z
  complexLogarithm→nonzero z = PT.rec (isPropComplexNonzero z)
    (λ { (w , value) → subst ComplexNonzero value (expℂ-nonzero w) })

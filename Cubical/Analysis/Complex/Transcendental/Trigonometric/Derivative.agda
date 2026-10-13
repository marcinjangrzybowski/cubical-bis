module Cubical.Analysis.Complex.Transcendental.Trigonometric.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Basic
open import Cubical.Analysis.Complex.Calculus.Derivative.Algebra
open import Cubical.Analysis.Complex.Calculus.Derivative.Chain
open import Cubical.Analysis.Complex.Calculus.Holomorphic
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Derivative
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Constants
import Cubical.Analysis.Complex.Transcendental.Trigonometric.Derivative.Algebra as Algebra

private
  module A = Algebra.EulerDerivativeAlgebra ℂCommRing

  positivePhase negativePhase positiveDerivative negativeDerivative : ℂ → ℂ
  positivePhase z = expℂ (iℂ ·ℂ z)
  negativePhase z = expℂ (-ℂ (iℂ ·ℂ z))
  positiveDerivative z = positivePhase z ·ℂ iℂ
  negativeDerivative z = negativePhase z ·ℂ (-ℂ iℂ)

  opaque
    positivePhaseHasDerivative : IsComplexDerivative positivePhase positiveDerivative
    positivePhaseHasDerivative = chainHasComplexDerivative
      (iℂ ·ℂ_) (λ _ → iℂ) expℂ expℂ
      (linearHasComplexDerivative iℂ) expℂHasSelfDerivative

    negativePhaseHasDerivative : IsComplexDerivative negativePhase negativeDerivative
    negativePhaseHasDerivative = chainHasComplexDerivative
      (λ z → -ℂ (iℂ ·ℂ z)) (λ _ → -ℂ iℂ) expℂ expℂ
      (negHasComplexDerivative (iℂ ·ℂ_) (λ _ → iℂ) (linearHasComplexDerivative iℂ))
      expℂHasSelfDerivative

    cosFormulaHasDerivative : IsComplexDerivative
      (λ z → cosFromExp (positivePhase z) (negativePhase z))
      (λ z → halfℂ ·ℂ (positiveDerivative z +ℂ negativeDerivative z))
    cosFormulaHasDerivative = chainHasComplexDerivative
      (λ z → positivePhase z +ℂ negativePhase z)
      (λ z → positiveDerivative z +ℂ negativeDerivative z)
      (halfℂ ·ℂ_) (λ _ → halfℂ)
      (addHasComplexDerivative positivePhase negativePhase positiveDerivative negativeDerivative
        positivePhaseHasDerivative negativePhaseHasDerivative)
      (linearHasComplexDerivative halfℂ)

    sinFormulaHasDerivative : IsComplexDerivative
      (λ z → sinFromExp (positivePhase z) (negativePhase z))
      (λ z → (-ℂ iℂ ·ℂ halfℂ) ·ℂ (positiveDerivative z -ℂ negativeDerivative z))
    sinFormulaHasDerivative = chainHasComplexDerivative
      (λ z → positivePhase z -ℂ negativePhase z)
      (λ z → positiveDerivative z -ℂ negativeDerivative z)
      ((-ℂ iℂ ·ℂ halfℂ) ·ℂ_) (λ _ → -ℂ iℂ ·ℂ halfℂ)
      (subHasComplexDerivative positivePhase negativePhase positiveDerivative negativeDerivative
        positivePhaseHasDerivative negativePhaseHasDerivative)
      (linearHasComplexDerivative (-ℂ iℂ ·ℂ halfℂ))

opaque
  -- Differentiate the existing two-exponential definitions. These are
  -- derivatives for arbitrary complex increments, not axis restrictions.
  cosℂHasDerivative : IsComplexDerivative cosℂ (λ z → -ℂ sinℂ z)
  cosℂHasDerivative = subst2 IsComplexDerivative
    (sym (funExt cosℂ-exp))
    (funExt (λ z → A.cosPair-derivative halfℂ iℂ (positivePhase z) (negativePhase z)
      ∙ cong -ℂ_ (sym (sinℂ-exp z))))
    cosFormulaHasDerivative

  sinℂHasDerivative : IsComplexDerivative sinℂ cosℂ
  sinℂHasDerivative = subst2 IsComplexDerivative
    (sym (funExt sinℂ-exp))
    (funExt (λ z → A.sinPair-derivative halfℂ iℂ i²≡-1 (positivePhase z) (negativePhase z)
      ∙ sym (cosℂ-exp z)))
    sinFormulaHasDerivative

  cosℂ-isEntire : IsEntire cosℂ
  cosℂ-isEntire = complexDerivativeGivesEntire cosℂ (λ z → -ℂ sinℂ z) cosℂHasDerivative

  sinℂ-isEntire : IsEntire sinℂ
  sinℂ-isEntire = complexDerivativeGivesEntire sinℂ cosℂ sinℂHasDerivative

module Cubical.Analysis.Complex.Transcendental.Logarithm.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Inverse
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Derivative

-- A continuous logarithmic branch is complex differentiable on its own
-- parameter space. Neither global norm bounds nor an ambient extension of
-- the branch are required. This theorem assumes the branch, not its derivative.
opaque
  logarithmBranchHasDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (coordinate logarithm reciprocal : A → ℂ) →
    (∀ x → expℂ (logarithm x) ≡ coordinate x) →
    (∀ x → reciprocal x ·ℂ coordinate x ≡ 1ℂ) →
    isContinuous source logarithm (ℂPremetricSpace .snd) →
    IsComplexDerivativeAlong source coordinate logarithm reciprocal
  logarithmBranchHasDerivativeAlong source coordinate logarithm reciprocal exponentialLaw reciprocalLaw continuous =
    inverseComplexDerivativeAlong source coordinate logarithm coordinate reciprocal reciprocalLaw
      (subst (λ h → IsComplexDerivativeAlong source logarithm h h) (funExt exponentialLaw)
        (pullbackComplexDerivativeAlong source (ℂPremetricSpace .snd)
          (idfun ℂ) expℂ expℂ logarithm continuous expℂHasSelfDerivative))

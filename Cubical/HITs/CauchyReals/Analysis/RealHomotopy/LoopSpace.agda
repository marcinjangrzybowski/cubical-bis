module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.LoopSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed.Base using (Pointed)
open import Cubical.Data.Sigma
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Base

PointedPremetricSpace : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
PointedPremetricSpace ℓ ℓ' = Σ[ X ∈ PremetricSpace ℓ ℓ' ] fst X

carrier∙ : ∀ {ℓ ℓ'} → PointedPremetricSpace ℓ ℓ' → Pointed ℓ
carrier∙ (X , x) = fst X , x

-- Loops are actual uniformly continuous real interval maps. We put the
-- rounded uniform premetric on them, before taking any homotopy quotient.
module RealLoops {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') (x : fst X) where
  open Paths X public

  RealLoop : Type (ℓ-max ℓ ℓ')
  RealLoop = UCPath x x

  private
    module L = SubspaceAlongInjection (→PremetricSpace 𝕀 X)
      (isSetUCPath x x) (λ (p : RealLoop) → at p)
      (λ p q same → path-ext {p = p} {q = q} (funExt⁻ same))

  realLoopSpace : PremetricSpace (ℓ-max ℓ ℓ') ℓ'
  realLoopSpace = L.injectionPremetricSpace

  constantLoop : RealLoop
  constantLoop = constantPath x

realΩ : ∀ {ℓ ℓ'} → PointedPremetricSpace ℓ ℓ' →
  PointedPremetricSpace (ℓ-max ℓ ℓ') ℓ'
realΩ (X , x) = RealLoops.realLoopSpace X x , RealLoops.constantLoop X x

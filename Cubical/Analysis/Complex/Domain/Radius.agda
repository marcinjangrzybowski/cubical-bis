module Cubical.Analysis.Complex.Domain.Radius where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Domain.OpenInterval
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Continuity

-- These domains use the submultiplicative l1 norm, as do the power-series
-- estimates. They are not definitions of Euclidean modulus disks.
ClosedComplexNormRadiusPredicate : ℝ → ℙ ℂ
ClosedComplexNormRadiusPredicate radius z = (normℂ z ≤ℝ radius) , isProp≤ℝ (normℂ z) radius

OpenComplexNormRadiusPredicate : ℝ → ℙ ℂ
OpenComplexNormRadiusPredicate radius = predicatePreimage normℂ (UpperOpenHalfLinePredicate radius)

ClosedComplexNormRadius : ℝ → Type₀
ClosedComplexNormRadius radius = Σ[ z ∈ ℂ ] normℂ z ≤ℝ radius

OpenComplexNormRadius : ℝ → Type₀
OpenComplexNormRadius radius = Σ[ z ∈ ℂ ] normℂ z <ℝ radius

ClosedComplexNormRadiusPremetricSpace : ℝ → PremetricSpace ℓ-zero ℓ-zero
ClosedComplexNormRadiusPremetricSpace radius = PremetricSubspace ℂPremetricSpace (ClosedComplexNormRadiusPredicate radius)

OpenComplexNormRadiusPremetricSpace : ℝ → PremetricSpace ℓ-zero ℓ-zero
OpenComplexNormRadiusPremetricSpace radius = PremetricSubspace ℂPremetricSpace (OpenComplexNormRadiusPredicate radius)

closedComplexNormRadiusInclusionNE : ∀ radius → NE[ ClosedComplexNormRadiusPremetricSpace radius , ℂPremetricSpace ]
closedComplexNormRadiusInclusionNE radius = subspaceInclusionNE ℂPremetricSpace (ClosedComplexNormRadiusPredicate radius)

openComplexNormRadiusInclusionNE : ∀ radius → NE[ OpenComplexNormRadiusPremetricSpace radius , ℂPremetricSpace ]
openComplexNormRadiusInclusionNE radius = subspaceInclusionNE ℂPremetricSpace (OpenComplexNormRadiusPredicate radius)

openComplexNormRadiusIsOpen : ∀ radius → IsOpenPredicate (ℂPremetricSpace .snd) (OpenComplexNormRadiusPredicate radius)
openComplexNormRadiusIsOpen radius = continuousPreimageIsOpen normℂ (UpperOpenHalfLinePredicate radius)
  normℂ-isContinuous (upperOpenHalfLineIsOpen radius)

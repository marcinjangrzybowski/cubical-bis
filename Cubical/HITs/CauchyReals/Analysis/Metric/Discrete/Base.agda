module Cubical.HITs.CauchyReals.Analysis.Metric.Discrete.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Relation.Premetric.Base using (PremetricSpace)
open import Cubical.Relation.Premetric.Mappings using (NE[_,_]; UC[_,_])
open import Cubical.Relation.Premetric.Instances.Unit


trivialPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
trivialPremetricSpace = UnitPremetricSpace


fromTrivialPremetricSpaceNE : ∀ {ℓ ℓ'}
  (A : PremetricSpace ℓ ℓ')
  (f : ⟨ trivialPremetricSpace ⟩ → ⟨ A ⟩) →
  NE[ trivialPremetricSpace , A ]
fromTrivialPremetricSpaceNE = fromUnitNE


fromTrivialPremetricSpaceUC : ∀ {ℓ ℓ'}
  (A : PremetricSpace ℓ ℓ')
  (f : ⟨ trivialPremetricSpace ⟩ → ⟨ A ⟩) →
  UC[ trivialPremetricSpace , A ]
fromTrivialPremetricSpaceUC = fromUnitUC

open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Equivalence
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Alternative M'
open import Cubical.Relation.Premetric.Completion.Alternative.Properties M'
open import Cubical.Relation.Premetric.Completion.Base M'
  renaming (ℭ to ℭM)


regularAlternativeEquiv : ℭM ≃ ℭ̂
regularAlternativeEquiv = isoToEquiv regularAlternativeIso

alternativeRegularEquiv : ℭ̂ ≃ ℭM
alternativeRegularEquiv = isoToEquiv (invIso regularAlternativeIso)


regularAlternativeIsometry : IsIsometry
  (Regular.ℭPremetricSpace .snd)
  regularAlternativeEquiv
  (ℭ̂PremetricSpace .snd)
regularAlternativeIsometry .IsIsometry.pres≈ x ε y =
  →̂-closenessEquiv x y ε

alternativeRegularIsometry : IsIsometry
  (ℭ̂PremetricSpace .snd)
  alternativeRegularEquiv
  (Regular.ℭPremetricSpace .snd)
alternativeRegularIsometry .IsIsometry.pres≈ x ε y =
  ←̂-closenessEquiv x y ε


regularAlternativePremetricEquiv :
  PremetricSpaceEquiv Regular.ℭPremetricSpace ℭ̂PremetricSpace
regularAlternativePremetricEquiv =
  regularAlternativeEquiv , regularAlternativeIsometry

alternativeRegularPremetricEquiv :
  PremetricSpaceEquiv ℭ̂PremetricSpace Regular.ℭPremetricSpace
alternativeRegularPremetricEquiv =
  alternativeRegularEquiv , alternativeRegularIsometry

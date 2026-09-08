module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareCancellation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding using (isEmbedding→hasPropFibers)
open import Cubical.HITs.Pushout.Base
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (𝟘)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareBoundary
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareDegeneracies
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareAttachment
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.LatchingAttachment
open CategoryStructures using (UC≡)

module SquareCancellation {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') where
  open SquareDegeneracies X
  open SquareAttachment X

  -- In particular this applies to a terminal premetric space. Work with
  -- the actual UC-square coefficients and the actual attaching map.
  module _ (propX : isProp (fst X)) where
    private
      degenerateRepresentative : (s : SquareCube) → fiber latchingMap s
      degenerateRepresentative s = inl (constant (fst s (𝟘 , 𝟘))) ,
        UC≡ (funExt (λ z → propX (fst s (𝟘 , 𝟘)) (fst s z)))

    propositionalLatchingEquiv : Latching₂ ≃ SquareCube
    fst propositionalLatchingEquiv = latchingMap
    equiv-proof (snd propositionalLatchingEquiv) s = degenerateRepresentative s ,
      isEmbedding→hasPropFibers isEmbeddingLatching₂ s (degenerateRepresentative s)

    propositionalAttachmentIso : Iso Realization₂ Realization₁
    propositionalAttachmentIso =
      degenerateAttachmentIso boundary₂ propositionalLatchingEquiv attach₂

    propositionalIncludeIsEquiv : isEquiv include₁
    propositionalIncludeIsEquiv = isoToIsEquiv (invIso propositionalAttachmentIso)

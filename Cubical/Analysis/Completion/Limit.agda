open import Cubical.Relation.Premetric.Base

module Cubical.Analysis.Completion.Limit
  {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition

module M = SequentialDefinition M'
module MP = SequentialPropertiesDefinition M'
module N = SequentialDefinition N'
module NP = SequentialPropertiesDefinition N'

private
  module NTheory = PremetricTheory NP.ℭ̂ₛPremetricSpace


-- Any continuous map preserves the limit represented by a `lim`
-- constructor.  An image witness is accepted explicitly because a merely
-- continuous function need not carry arbitrary Cauchy sequences to Cauchy
-- sequences without using their convergence.

continuous-map-lim :
  (f : M.ℭ̂ₛ → N.ℭ̂ₛ) →
  isContinuous
    (MP.ℭ̂ₛPremetricSpace .snd) f
    (NP.ℭ̂ₛPremetricSpace .snd) →
  ∀ x gx (imageWitness : N.SeqWitness (f ∘ x)) →
  f (M.lim x gx) ≡ N.lim (f ∘ x) imageWitness
continuous-map-lim f f-cont x gx imageWitness =
  cong fst
    (NTheory.isPropLimitSeq (f ∘ x)
      ( f (M.lim x gx)
      , C→seqContinuous (f , f-cont) x (M.lim x gx)
          (MP.lim-isLimitSeq x gx))
      ( N.lim (f ∘ x) imageWitness
      , NP.lim-isLimitSeq (f ∘ x) imageWitness))


-- Non-expanding maps provide the image witness themselves.  This is the
-- preferred limit rule for non-expanding lifts: it retains their exact
-- modulus instead of forgetting it through ordinary continuity.

mapSeqWitnessNonExpanding :
  (f : NE[ MP.ℭ̂ₛPremetricSpace , NP.ℭ̂ₛPremetricSpace ]) →
  ∀ {x} → M.SeqWitness x → N.SeqWitness (fst f ∘ x)
mapSeqWitnessNonExpanding f =
  PT.map (NE→presIsCauchySeq f _)

nonExpanding-map-lim :
  (f : NE[ MP.ℭ̂ₛPremetricSpace , NP.ℭ̂ₛPremetricSpace ]) →
  ∀ x gx →
  fst f (M.lim x gx) ≡
    N.lim (fst f ∘ x) (mapSeqWitnessNonExpanding f gx)
nonExpanding-map-lim f x gx =
  continuous-map-lim (fst f)
    (isNonExpanding→isContinuous
      (MP.ℭ̂ₛPremetricSpace .snd) (fst f)
      (NP.ℭ̂ₛPremetricSpace .snd) (snd f))
    x gx (mapSeqWitnessNonExpanding f gx)

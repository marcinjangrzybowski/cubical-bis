open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.UniversalProperty.Instances.CauchySequence
  {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.UniversalProperty.Base
import Cubical.Relation.Premetric.Completion.UniversalProperty.CompletionCentered
  as GenericCenteredDefinition
import Cubical.Relation.Premetric.Completion.UniversalProperty.NonExpanding
  as GenericNonExpandingDefinition

import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion
import Cubical.Relation.Premetric.Completion.CauchySequence.Approximation
  as CauchyApproximation
import Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  as CauchyPremetric
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CompletionCentered
  as ConcreteCenteredDefinition
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.UniversalProperty
  as ConcreteNonExpandingDefinition
import Cubical.Relation.Premetric.Completion.CauchySequence.Limits
  as CauchySequenceLimits

module S = CauchyCompletion M'
module SA = CauchyApproximation M'
module SP = CauchyPremetric M'
module T = CauchyCompletion N'
module TP = CauchyPremetric N'
module PM = PremetricStr (M' .snd)

private
  ℓC = ℓ-max ℓM ℓM'


-- Initializing the construction-independent presentation is just the
-- completed premetric, injection, isometry law, and density proof.

cauchySequenceCompletionPresentation :
  CompletionPresentation M' ℓC ℓC
cauchySequenceCompletionPresentation .completionSpace =
  SP.CompletionPremetricSpace
cauchySequenceCompletionPresentation .injection = S.ι
cauchySequenceCompletionPresentation .injection-pres≈ x y ε =
  propBiimpl→Equiv
    (PM.isProp≈ x y ε)
    (S.isProp≈ᶜ (S.ι x) ε (S.ι y))
    (S.ι-ι x y ε)
    (SA.ι-ι→≈ x y ε)
cauchySequenceCompletionPresentation .dense = SP.∃approx


module CompletionCenteredProperty = GenericCenteredDefinition
  M' cauchySequenceCompletionPresentation TP.CompletionPremetricSpace

module ConcreteCompletionCentered = ConcreteCenteredDefinition M' N'


-- The old construction-specific predicate and the generic predicate are
-- definitionally the same statement apart from their record wrappers.

generic→concrete : ∀ {f} →
  CompletionCenteredProperty.IsCompletionCenteredContinuous f →
  ConcreteCompletionCentered.IsCompletionCenteredContinuous f
generic→concrete centered
  .ConcreteCompletionCentered.IsCompletionCenteredContinuous.at =
  centered .CompletionCenteredProperty.IsCompletionCenteredContinuous.at

concrete→generic : ∀ {f} →
  ConcreteCompletionCentered.IsCompletionCenteredContinuous f →
  CompletionCenteredProperty.IsCompletionCenteredContinuous f
concrete→generic centered
  .CompletionCenteredProperty.IsCompletionCenteredContinuous.at =
  centered .ConcreteCompletionCentered.IsCompletionCenteredContinuous.at

completionCenteredPredicateEquiv : ∀ f →
  CompletionCenteredProperty.IsCompletionCenteredContinuous f ≃
  ConcreteCompletionCentered.IsCompletionCenteredContinuous f
completionCenteredPredicateEquiv f =
  propBiimpl→Equiv
    (CompletionCenteredProperty.isPropIsCompletionCenteredContinuous f)
    (ConcreteCompletionCentered.isPropIsCompletionCenteredContinuous f)
    generic→concrete concrete→generic


-- This single value initializes every generic classification and uniqueness
-- result below for the CauchySequence construction.

hasCompletionCenteredUniversalProperty :
  CompletionCenteredProperty.HasCompletionCenteredUniversalProperty
hasCompletionCenteredUniversalProperty =
  CompletionCenteredProperty.makeCompletionCenteredUniversalProperty
    extend continuous computes
  where
  extend : ∀ f →
    CompletionCenteredProperty.IsCompletionCenteredContinuous f →
    S.Completion → T.Completion
  extend f centered =
    ConcreteCompletionCentered.extendCompletionCentered f
      (generic→concrete centered)

  continuous : ∀ f centered →
    isContinuous
      (SP.CompletionPremetricSpace .snd)
      (extend f centered)
      (TP.CompletionPremetricSpace .snd)
  continuous f centered =
    ConcreteCompletionCentered.extendCompletionCentered-isContinuous f
      (generic→concrete centered)

  computes : ∀ f centered q →
    extend f centered (S.ι q) ≡ f q
  computes f centered =
    ConcreteCompletionCentered.extendCompletionCentered-ι f
      (generic→concrete centered)


module CompletionCenteredMappingSpace =
  CompletionCenteredProperty.WithUniversalProperty
    hasCompletionCenteredUniversalProperty


-- The ordinary universal property has a different target and a different
-- map class.  For every premetric target equipped with radiuswise Cauchy-
-- sequence limits, restriction along ι is an equivalence on nonexpanding
-- maps.  Keeping it in its own namespace prevents confusing it with the
-- completion-centered classification above.

module NonExpanding
  (complete : CauchySequenceLimits.HasCauchySequenceLimits N') where

  module GenericProperty = GenericNonExpandingDefinition
    M' cauchySequenceCompletionPresentation N'

  module ConcreteLift = ConcreteNonExpandingDefinition M' N'

  hasUniversalProperty :
    GenericProperty.HasNonExpandingUniversalProperty
  hasUniversalProperty =
    GenericProperty.makeNonExpandingUniversalProperty
      (ConcreteLift.liftNonExpanding complete)
      (ConcreteLift.liftNonExpanding-ι complete)

  module MappingSpace =
    GenericProperty.WithUniversalProperty hasUniversalProperty

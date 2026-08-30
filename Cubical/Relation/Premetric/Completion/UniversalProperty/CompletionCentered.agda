open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Completion.UniversalProperty.Base

module Cubical.Relation.Premetric.Completion.UniversalProperty.CompletionCentered
  {ℓM ℓM' ℓC ℓC' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (P : CompletionPresentation M' ℓC ℓC')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Relation.Premetric.Mappings
import Cubical.Relation.Premetric.Completion.UniversalProperty.Extensionality
  as ExtensionalityDefinition

private
  M = M' .fst
  C' = P .completionSpace
  C = C' .fst
  N = N' .fst
  ι = P .injection
  ℓradius = ℓ-max ℓM (ℓ-max ℓC' ℓN')
  ℓcenter = ℓ-max ℓC ℓradius
  ℓextends = ℓ-max ℓM ℓN
  ℓproperty =
    ℓ-max (ℓ-max ℓM ℓN) (ℓ-max ℓC (ℓ-max ℓC' ℓN'))
  ℓrestriction = ℓproperty
  ℓcontinuousMap =
    ℓ-max (ℓ-max ℓC ℓN) (ℓ-max ℓC' ℓN')

module PC = PremetricStr (C' .snd)
module PN = PremetricStr (N' .snd)
module Extensionality = ExtensionalityDefinition M' P N'

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


-- This definition refers only to a presented dense completion, not to its
-- constructors, recursors, or chosen representation of limits.

CenteredRadiusFor : (M → N) → C → ℚ₊ → Type ℓradius
CenteredRadiusFor f x ε =
  Σ[ δ ∈ ℚ₊ ]
    (∀ q r →
      ι q PC.≈[ δ ] x →
      ι r PC.≈[ δ ] x →
      f q PN.≈[ ε ] f r)


record IsCompletionCenteredContinuous (f : M → N) : Type ℓcenter where
  no-eta-equality
  field
    at : ∀ x ε → ∥ CenteredRadiusFor f x ε ∥₁

open IsCompletionCenteredContinuous


isPropIsCompletionCenteredContinuous : ∀ f →
  isProp (IsCompletionCenteredContinuous f)
isPropIsCompletionCenteredContinuous f a b i .at x ε =
  squash₁ (a .at x ε) (b .at x ε) i


-- Restriction of an ordinary continuous map is completion-centered.  This
-- direction does not need density or any extension principle.

continuous→completionCenteredRestriction :
  ∀ (F : C → N) →
  isContinuous (C' .snd) F (N' .snd) →
  IsCompletionCenteredContinuous (F ∘ ι)
continuous→completionCenteredRestriction F F-cont .at x ε =
  PT.map withRadius
    (F-cont x .IsContinuousAt.pres≈ (ε /2₊))
  where
  withRadius :
    (Σ[ δ ∈ ℚ₊ ]
      (∀ y → x PC.≈[ δ ] y →
        F x PN.≈[ ε /2₊ ] F y)) →
    CenteredRadiusFor (F ∘ ι) x ε
  withRadius (δ , preserve) = δ , λ q r ιq≈x ιr≈x →
    PN.subst≈ (F (ι q)) (F (ι r))
      (/2+/2≡id (fst ε))
      (PN.isTriangular≈ (F (ι q)) (F x) (F (ι r))
        (ε /2₊) (ε /2₊)
        (PN.isSym≈ (F x) (F (ι q)) (ε /2₊)
          (preserve (ι q)
            (PC.isSym≈ (ι q) x δ ιq≈x)))
        (preserve (ι r)
          (PC.isSym≈ (ι r) x δ ιr≈x)))


-- Density is enough for uniqueness: continuous maps from the completion
-- are determined by their values on the presented base.

continuousMap-ext :
  ∀ (F G : C → N) →
  isContinuous (C' .snd) F (N' .snd) →
  isContinuous (C' .snd) G (N' .snd) →
  (∀ q → F (ι q) ≡ G (ι q)) →
  F ≡ G
continuousMap-ext = Extensionality.continuousMap-ext


ExtendsRestriction : (M → N) → (C → N) → Type ℓextends
ExtendsRestriction f F = ∀ q → F (ι q) ≡ f q

isPropExtendsRestriction : ∀ f F →
  isProp (ExtendsRestriction f F)
isPropExtendsRestriction f F =
  isPropΠ λ _ → PN.isSetM _ _


IsContinuousExtension : (M → N) → (C → N) → Type ℓproperty
IsContinuousExtension f F =
  isContinuous (C' .snd) F (N' .snd) ×
  ExtendsRestriction f F

isPropIsContinuousExtension : ∀ f F →
  isProp (IsContinuousExtension f F)
isPropIsContinuousExtension f F = isProp×
  (isPropIsContinuous (C' .snd) F (N' .snd))
  (isPropExtendsRestriction f F)


ContinuousExtension : (M → N) → Type ℓproperty
ContinuousExtension f =
  Σ[ F ∈ (C → N) ] IsContinuousExtension f F


isPropContinuousExtension : ∀ f → isProp (ContinuousExtension f)
isPropContinuousExtension f
  E@(F , F-cont , F-ι) E'@(G , G-cont , G-ι) =
  Σ≡Prop (isPropIsContinuousExtension f)
    (continuousMap-ext F G F-cont G-cont
      (λ q → F-ι q ∙ sym (G-ι q)))


-- Universal property for this class of maps: every centered restriction has
-- its necessarily unique continuous extension.

HasCompletionCenteredUniversalProperty : Type ℓproperty
HasCompletionCenteredUniversalProperty =
  ∀ f → IsCompletionCenteredContinuous f → ContinuousExtension f

isPropHasCompletionCenteredUniversalProperty :
  isProp HasCompletionCenteredUniversalProperty
isPropHasCompletionCenteredUniversalProperty =
  isPropΠ2 λ f _ → isPropContinuousExtension f


-- Convenience initializer for a concrete construction.  It only asks for
-- an extension operator and its two observable laws.

makeCompletionCenteredUniversalProperty :
  (extend : (f : M → N) →
    IsCompletionCenteredContinuous f → C → N) →
  (∀ f centered →
    isContinuous (C' .snd) (extend f centered) (N' .snd)) →
  (∀ f centered q → extend f centered (ι q) ≡ f q) →
  HasCompletionCenteredUniversalProperty
makeCompletionCenteredUniversalProperty extend continuous computes
  f centered =
  extend f centered , continuous f centered , computes f centered


module WithUniversalProperty
  (universal : HasCompletionCenteredUniversalProperty) where

  completionCenteredContinuous≃continuousExtension : ∀ f →
    IsCompletionCenteredContinuous f ≃ ContinuousExtension f
  completionCenteredContinuous≃continuousExtension f =
    propBiimpl→Equiv
      (isPropIsCompletionCenteredContinuous f)
      (isPropContinuousExtension f)
      (universal f)
      (λ (F , F-cont , F-ι) →
        subst IsCompletionCenteredContinuous
          (funExt F-ι)
          (continuous→completionCenteredRestriction F F-cont))


  CompletionCenteredRestriction : Type ℓrestriction
  CompletionCenteredRestriction =
    Σ[ f ∈ (M → N) ] IsCompletionCenteredContinuous f

  ContinuousMap : Type ℓcontinuousMap
  ContinuousMap =
    Σ[ F ∈ (C → N) ]
      isContinuous (C' .snd) F (N' .snd)

  RestrictionWithContinuousExtension : Type ℓproperty
  RestrictionWithContinuousExtension =
    Σ[ f ∈ (M → N) ] ContinuousExtension f

  completionCenteredRestrictionExtensionEquiv :
    CompletionCenteredRestriction ≃ RestrictionWithContinuousExtension
  completionCenteredRestrictionExtensionEquiv =
    Σ-cong-equiv-snd
      completionCenteredContinuous≃continuousExtension

  forgetRestriction : RestrictionWithContinuousExtension → ContinuousMap
  forgetRestriction (_ , F , F-cont , _) = F , F-cont

  attachRestriction : ContinuousMap → RestrictionWithContinuousExtension
  attachRestriction (F , F-cont) =
    F ∘ ι , F , F-cont , λ _ → refl

  restrictionWithContinuousExtensionMapIso :
    Iso RestrictionWithContinuousExtension ContinuousMap
  restrictionWithContinuousExtensionMapIso .Iso.fun = forgetRestriction
  restrictionWithContinuousExtensionMapIso .Iso.inv = attachRestriction
  restrictionWithContinuousExtensionMapIso .Iso.sec _ = refl
  restrictionWithContinuousExtensionMapIso .Iso.ret
    (f , F , F-cont , F-ι) =
    Σ≡Prop isPropContinuousExtension (funExt F-ι)

  completionCenteredRestrictionContinuousMapEquiv :
    CompletionCenteredRestriction ≃ ContinuousMap
  completionCenteredRestrictionContinuousMapEquiv =
    completionCenteredRestrictionExtensionEquiv
    ∙ₑ isoToEquiv restrictionWithContinuousExtensionMapIso

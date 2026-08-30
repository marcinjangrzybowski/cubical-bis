open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Completion.UniversalProperty.Base

module Cubical.Relation.Premetric.Completion.UniversalProperty.NonExpanding
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

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures

import Cubical.Relation.Premetric.Completion.UniversalProperty.Extensionality
  as ExtensionalityDefinition

private
  M = M' .fst
  C' = P .completionSpace
  C = C' .fst
  N = N' .fst
  ι = P .injection
  ℓextends = ℓ-max ℓM ℓN
  ℓextension =
    ℓ-max (ℓ-max ℓM ℓC) (ℓ-max ℓN (ℓ-max ℓC' ℓN'))
  ℓuniversal = ℓ-max ℓM' ℓextension

module Extensionality = ExtensionalityDefinition M' P N'


injectionⁿ : NE[ M' , C' ]
injectionⁿ .fst = ι
injectionⁿ .snd .IsNonExpanding.pres≈ x y ε =
  equivFun (P .injection-pres≈ x y ε)


restrictNonExpanding : NE[ C' , N' ] → NE[ M' , N' ]
restrictNonExpanding F .fst = fst F ∘ ι
restrictNonExpanding F .snd .IsNonExpanding.pres≈ x y ε x≈y =
  F .snd .IsNonExpanding.pres≈ (ι x) (ι y) ε
    (equivFun (P .injection-pres≈ x y ε) x≈y)


ExtendsRestriction :
  NE[ M' , N' ] → NE[ C' , N' ] → Type ℓextends
ExtendsRestriction f F =
  ∀ q → fst F (ι q) ≡ fst f q

isPropExtendsRestriction : ∀ f F →
  isProp (ExtendsRestriction f F)
isPropExtendsRestriction f F =
  isPropΠ λ _ → PremetricStr.isSetM (N' .snd) _ _


NonExpandingExtension : NE[ M' , N' ] → Type ℓextension
NonExpandingExtension f =
  Σ[ F ∈ NE[ C' , N' ] ] ExtendsRestriction f F


isPropNonExpandingExtension : ∀ f →
  isProp (NonExpandingExtension f)
isPropNonExpandingExtension f
  (F , F-ι) (G , G-ι) =
  Σ≡Prop (isPropExtendsRestriction f)
    (Extensionality.nonExpandingMap-ext F G
      (λ q → F-ι q ∙ sym (G-ι q)))


-- Every nonexpanding base map has its necessarily unique nonexpanding
-- extension.  This is the universal-arrow formulation before packaging it
-- as an equivalence of mapping spaces.

HasNonExpandingUniversalProperty : Type ℓuniversal
HasNonExpandingUniversalProperty =
  ∀ f → NonExpandingExtension f

isPropHasNonExpandingUniversalProperty :
  isProp HasNonExpandingUniversalProperty
isPropHasNonExpandingUniversalProperty =
  isPropΠ isPropNonExpandingExtension


makeNonExpandingUniversalProperty :
  (extend : NE[ M' , N' ] → NE[ C' , N' ]) →
  (∀ f q → fst (extend f) (ι q) ≡ fst f q) →
  HasNonExpandingUniversalProperty
makeNonExpandingUniversalProperty extend computes f =
  extend f , computes f


module WithUniversalProperty
  (universal : HasNonExpandingUniversalProperty) where

  liftNonExpanding : NE[ M' , N' ] → NE[ C' , N' ]
  liftNonExpanding f = universal f .fst

  liftNonExpanding-ι : ∀ f q →
    fst (liftNonExpanding f) (ι q) ≡ fst f q
  liftNonExpanding-ι f = universal f .snd

  restrictAfterLift : ∀ f →
    restrictNonExpanding (liftNonExpanding f) ≡ f
  restrictAfterLift f =
    NE≡ (funExt (liftNonExpanding-ι f))

  liftAfterRestrict : ∀ F →
    liftNonExpanding (restrictNonExpanding F) ≡ F
  liftAfterRestrict F =
    Extensionality.nonExpandingMap-ext
      (liftNonExpanding (restrictNonExpanding F)) F
      (liftNonExpanding-ι (restrictNonExpanding F))

  nonExpandingExtensionIso :
    Iso NE[ M' , N' ] NE[ C' , N' ]
  nonExpandingExtensionIso .Iso.fun = liftNonExpanding
  nonExpandingExtensionIso .Iso.inv = restrictNonExpanding
  nonExpandingExtensionIso .Iso.sec = liftAfterRestrict
  nonExpandingExtensionIso .Iso.ret = restrictAfterLift

  nonExpandingExtensionEquiv :
    NE[ M' , N' ] ≃ NE[ C' , N' ]
  nonExpandingExtensionEquiv =
    isoToEquiv nonExpandingExtensionIso

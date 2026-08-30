open import Cubical.Relation.Premetric.Base

module Cubical.Analysis.Completion.NonExpanding
  {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Premetric.Mappings

import Cubical.Analysis.Completion.Extensionality
  as ExtensionalityDefinition
import Cubical.Relation.Premetric.Completion.Properties.Lift
  as RegularLiftDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as ComparisonDefinition

module M = SequentialDefinition M'
module MP = SequentialPropertiesDefinition M'
module N = SequentialDefinition N'
module NP = SequentialPropertiesDefinition N'
module MC = ComparisonDefinition M'
module NC = ComparisonDefinition N'
module Ext = ExtensionalityDefinition M'
module RegularLift = RegularLiftDefinition.Liftℭ M' N'

open CategoryStructures


private
  toRegularMⁿ : NE[ MP.ℭ̂ₛPremetricSpace , MC.C.ℭPremetricSpace ]
  toRegularMⁿ = MC.toRegular ,
    isIsometry→IsNonExpanding
      (MP.ℭ̂ₛPremetricSpace .snd)
      MC.sequentialRegularEquiv
      (MC.C.ℭPremetricSpace .snd)
      MC.sequentialRegularIsometry

  fromRegularNⁿ : NE[ NC.C.ℭPremetricSpace , NP.ℭ̂ₛPremetricSpace ]
  fromRegularNⁿ = NC.fromRegular ,
    isIsometry→IsNonExpanding
      (NC.C.ℭPremetricSpace .snd)
      NC.regularSequentialEquiv
      (NP.ℭ̂ₛPremetricSpace .snd)
      NC.regularSequentialIsometry

module Construction (fⁿ : NE[ M' , N' ]) where

  private
    f = fst fⁿ

    regularBaseⁿ : NE[ M' , NC.C.ℭPremetricSpace ]
    regularBaseⁿ = RegularLiftDefinition.ιⁿ ∘NE fⁿ

    regularLiftⁿ :
      NE[ MC.C.ℭPremetricSpace , NC.C.ℭPremetricSpace ]
    regularLiftⁿ = RegularLift.liftNonExpandingℭ regularBaseⁿ

  transportedⁿ : NE[ MP.ℭ̂ₛPremetricSpace , NP.ℭ̂ₛPremetricSpace ]
  transportedⁿ =
    fromRegularNⁿ ∘NE (regularLiftⁿ ∘NE toRegularMⁿ)

  transported-ι : ∀ q →
    fst transportedⁿ (M.ι q) ≡ N.ι (f q)
  transported-ι q =
    cong (NC.fromRegular ∘ fst regularLiftⁿ) (MC.toRegular-ι q)
    ∙ cong NC.fromRegular
        (funExt⁻ (RegularLift.liftⁿℭ∘ι regularBaseⁿ) q)
    ∙ NC.fromRegular-ι (f q)

  -- Compatibility surface: the implementation now uses a single transported
  -- lift, but clients of Construction retain the original names.
  sequentialFunction : M.ℭ̂ₛ → N.ℭ̂ₛ
  sequentialFunction = fst transportedⁿ

  sequentialFunction-ι : ∀ q →
    sequentialFunction (M.ι q) ≡ N.ι (f q)
  sequentialFunction-ι = transported-ι

  sequential-isNonExpanding : IsNonExpanding
    (MP.ℭ̂ₛPremetricSpace .snd) sequentialFunction
    (NP.ℭ̂ₛPremetricSpace .snd)
  sequential-isNonExpanding = snd transportedⁿ


liftNonExpanding :
  NE[ M' , N' ] → NE[ MP.ℭ̂ₛPremetricSpace , NP.ℭ̂ₛPremetricSpace ]
liftNonExpanding fⁿ =
  Construction.sequentialFunction fⁿ ,
  Construction.sequential-isNonExpanding fⁿ

liftNonExpanding-ι : ∀ fⁿ q →
  fst (liftNonExpanding fⁿ) (M.ι q) ≡ N.ι (fst fⁿ q)
liftNonExpanding-ι = Construction.sequentialFunction-ι

liftNonExpanding-ext :
  (fⁿ gⁿ : NE[ M' , N' ]) →
  (∀ q → fst fⁿ q ≡ fst gⁿ q) →
  liftNonExpanding fⁿ ≡ liftNonExpanding gⁿ
liftNonExpanding-ext fⁿ gⁿ on-base = NE≡
  (Ext.nonExpandingExtensionality NP.ℭ̂ₛPremetricSpace
    (fst (liftNonExpanding fⁿ)) (fst (liftNonExpanding gⁿ))
    (snd (liftNonExpanding fⁿ)) (snd (liftNonExpanding gⁿ))
    λ q →
      liftNonExpanding-ι fⁿ q
      ∙ cong N.ι (on-base q)
      ∙ sym (liftNonExpanding-ι gⁿ q))

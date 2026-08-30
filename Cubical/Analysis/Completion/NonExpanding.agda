open import Cubical.Relation.Premetric.Base

module Cubical.Analysis.Completion.NonExpanding
  {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.HITs.PropositionalTruncation as PT

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
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.UniformlyContinuous
  as UniformlyContinuousDefinition

module M = SequentialDefinition M'
module MP = SequentialPropertiesDefinition M'
module N = SequentialDefinition N'
module NP = SequentialPropertiesDefinition N'
module MC = ComparisonDefinition M'
module NC = ComparisonDefinition N'
module U = UniformlyContinuousDefinition M' N'
module Ext = ExtensionalityDefinition M'
module RegularLift = RegularLiftDefinition.Liftℭ M' N'

open CategoryStructures
open PositiveRationals


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

  identityModulus : ℚ₊ → ℚ₊
  identityModulus ε = ε


module Construction (fⁿ : NE[ M' , N' ]) where

  private
    f = fst fⁿ

    f-uc-with : IsUniformlyContinuousWith
      (M' .snd) f (N' .snd) identityModulus
    f-uc-with .IsUniformlyContinuousWith.pres≈ x y ε =
      fⁿ .snd .IsNonExpanding.pres≈ x y ε

  sequentialFunction : M.ℭ̂ₛ → N.ℭ̂ₛ
  sequentialFunction =
    U.WithModulus.liftUniformlyContinuousWith
      f identityModulus f-uc-with

  sequentialFunction-ι : ∀ q →
    sequentialFunction (M.ι q) ≡ N.ι (f q)
  sequentialFunction-ι =
    U.WithModulus.liftUniformlyContinuousWith-ι
      f identityModulus f-uc-with

  private
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

    sequential-isContinuous : isContinuous
      (MP.ℭ̂ₛPremetricSpace .snd) sequentialFunction
      (NP.ℭ̂ₛPremetricSpace .snd)
    sequential-isContinuous =
      isUniformlyContinuous→isContinuous
        (MP.ℭ̂ₛPremetricSpace .snd) sequentialFunction
        (NP.ℭ̂ₛPremetricSpace .snd)
        ∣ U.WithModulus.inputBudget f identityModulus f-uc-with
        , U.WithModulus.liftUniformlyContinuousWith-isUniformlyContinuousWith
            f identityModulus f-uc-with ∣₁

    sequential≡transported : sequentialFunction ≡ fst transportedⁿ
    sequential≡transported =
      Ext.continuousExtensionality NP.ℭ̂ₛPremetricSpace
        sequentialFunction (fst transportedⁿ)
        sequential-isContinuous
        (isNonExpanding→isContinuous
          (MP.ℭ̂ₛPremetricSpace .snd) (fst transportedⁿ)
          (NP.ℭ̂ₛPremetricSpace .snd) (snd transportedⁿ))
        λ q →
          U.WithModulus.liftUniformlyContinuousWith-ι
            f identityModulus f-uc-with q
          ∙ sym (transported-ι q)

  sequential-isNonExpanding : IsNonExpanding
    (MP.ℭ̂ₛPremetricSpace .snd) sequentialFunction
    (NP.ℭ̂ₛPremetricSpace .snd)
  sequential-isNonExpanding = subst
    (λ h → IsNonExpanding
      (MP.ℭ̂ₛPremetricSpace .snd) h
      (NP.ℭ̂ₛPremetricSpace .snd))
    (sym sequential≡transported) (snd transportedⁿ)


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

open import Cubical.Relation.Premetric.Base

module Cubical.Analysis.Completion.Lipschitz
  {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

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

module M = SequentialDefinition M'
module MP = SequentialPropertiesDefinition M'
module N = SequentialDefinition N'
module NP = SequentialPropertiesDefinition N'
module MC = ComparisonDefinition M'
module NC = ComparisonDefinition N'
module Ext = ExtensionalityDefinition M'
module RegularLift = RegularLiftDefinition.Liftℭ M' N'

open PositiveRationals


private
  toRegularM-isNonExpanding : IsNonExpanding
    (MP.ℭ̂ₛPremetricSpace .snd) MC.toRegular
    (MC.C.ℭPremetricSpace .snd)
  toRegularM-isNonExpanding =
    isIsometry→IsNonExpanding
      (MP.ℭ̂ₛPremetricSpace .snd)
      MC.sequentialRegularEquiv
      (MC.C.ℭPremetricSpace .snd)
      MC.sequentialRegularIsometry

  fromRegularN-isNonExpanding : IsNonExpanding
    (NC.C.ℭPremetricSpace .snd) NC.fromRegular
    (NP.ℭ̂ₛPremetricSpace .snd)
  fromRegularN-isNonExpanding =
    isIsometry→IsNonExpanding
      (NC.C.ℭPremetricSpace .snd)
      NC.regularSequentialEquiv
      (NP.ℭ̂ₛPremetricSpace .snd)
      NC.regularSequentialIsometry


module Construction
  (L : ℚ₊)
  (f : M' .fst → N' .fst)
  (f-lip : IsLipschitzWith (M' .snd) f (N' .snd) L)
  where

  private
    regularBase : M' .fst → NC.Regular.ℭ
    regularBase q = NC.Regular.ι (f q)

    regularBase-isLipschitz : IsLipschitzWith
      (M' .snd) regularBase (NC.C.ℭPremetricSpace .snd) L
    regularBase-isLipschitz .IsLipschitzWith.pres≈ x y ε x≈y =
      RegularLiftDefinition.ιⁿ .snd .IsNonExpanding.pres≈
        (f x) (f y) (L ·₊ ε)
        (f-lip .IsLipschitzWith.pres≈ x y ε x≈y)

    regularLift : MC.Regular.ℭ → NC.Regular.ℭ
    regularLift = fst
      (RegularLift.liftLipschitzWithℭ
        L regularBase regularBase-isLipschitz)

    regularLift-isLipschitz : IsLipschitzWith
      (MC.C.ℭPremetricSpace .snd) regularLift
      (NC.C.ℭPremetricSpace .snd) L
    regularLift-isLipschitz = snd
      (RegularLift.liftLipschitzWithℭ
        L regularBase regularBase-isLipschitz)

  transported : M.ℭ̂ₛ → N.ℭ̂ₛ
  transported = NC.fromRegular ∘ regularLift ∘ MC.toRegular

  transported-isLipschitz : IsLipschitzWith
    (MP.ℭ̂ₛPremetricSpace .snd) transported
    (NP.ℭ̂ₛPremetricSpace .snd) L
  transported-isLipschitz .IsLipschitzWith.pres≈ x y ε x≈y =
    fromRegularN-isNonExpanding .IsNonExpanding.pres≈
      (regularLift (MC.toRegular x))
      (regularLift (MC.toRegular y))
      (L ·₊ ε)
      (regularLift-isLipschitz .IsLipschitzWith.pres≈
        (MC.toRegular x) (MC.toRegular y) ε
        (toRegularM-isNonExpanding .IsNonExpanding.pres≈
          x y ε x≈y))

  transported-ι : ∀ q →
    transported (M.ι q) ≡ N.ι (f q)
  transported-ι q =
      cong (NC.fromRegular ∘ regularLift) (MC.toRegular-ι q)
    ∙ cong NC.fromRegular
        (funExt⁻
          (RegularLift.liftℭ∘ι
            (regularBase ,
              ∣ L , regularBase-isLipschitz ∣₁)) q)
    ∙ NC.fromRegular-ι (f q)


liftLipschitzWith : ∀ L (f : M' .fst → N' .fst) →
  IsLipschitzWith (M' .snd) f (N' .snd) L →
  Σ[ F ∈ (M.ℭ̂ₛ → N.ℭ̂ₛ) ]
    IsLipschitzWith
      (MP.ℭ̂ₛPremetricSpace .snd) F
      (NP.ℭ̂ₛPremetricSpace .snd) L
liftLipschitzWith L f f-lip =
  Construction.transported L f f-lip ,
  Construction.transported-isLipschitz L f f-lip

liftLipschitzWith-ι : ∀ L f f-lip q →
  fst (liftLipschitzWith L f f-lip) (M.ι q) ≡ N.ι (f q)
liftLipschitzWith-ι = Construction.transported-ι

liftLipschitzWith-ext :
  ∀ L K f g
    (f-lip : IsLipschitzWith (M' .snd) f (N' .snd) L)
    (g-lip : IsLipschitzWith (M' .snd) g (N' .snd) K) →
  (∀ q → f q ≡ g q) →
  fst (liftLipschitzWith L f f-lip) ≡
  fst (liftLipschitzWith K g g-lip)
liftLipschitzWith-ext L K f g f-lip g-lip on-base =
  Ext.lipschitzExtensionality NP.ℭ̂ₛPremetricSpace
    (fst (liftLipschitzWith L f f-lip))
    (fst (liftLipschitzWith K g g-lip))
    ∣ L , snd (liftLipschitzWith L f f-lip) ∣₁
    ∣ K , snd (liftLipschitzWith K g g-lip) ∣₁
    λ q →
      liftLipschitzWith-ι L f f-lip q
      ∙ cong N.ι (on-base q)
      ∙ sym (liftLipschitzWith-ι K g g-lip q)

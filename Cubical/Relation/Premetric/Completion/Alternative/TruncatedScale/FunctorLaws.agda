open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale.FunctorLaws
  {ℓM ℓM' ℓN ℓN' ℓO ℓO'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN')
  (O' : PremetricSpace ℓO ℓO') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale
  as TruncatedScaleDefinition
import Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale.Properties
  as TruncatedScalePropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale.Functor
  as TruncatedScaleFunctorDefinition

module RM = TruncatedScaleDefinition M'
module RN = TruncatedScaleDefinition N'
module RO = TruncatedScaleDefinition O'

module PM = TruncatedScalePropertiesDefinition M'
module PN = TruncatedScalePropertiesDefinition N'
module PO = TruncatedScalePropertiesDefinition O'

module FMM = TruncatedScaleFunctorDefinition M' M'
module FMN = TruncatedScaleFunctorDefinition M' N'
module FNO = TruncatedScaleFunctorDefinition N' O'
module FMO = TruncatedScaleFunctorDefinition M' O'

open PositiveRationals

private
  M = M' .fst
  N = N' .fst
  O = O' .fst
  module PBaseO = PremetricStr (O' .snd)


-- The identity law needs only induction on points.  At a limit, equality of
-- the recursively mapped families is enough: their ScaleWitnesses disappear
-- propositionally.

private
  id-lip : IsLipschitzWith (M' .snd) (idfun M) (M' .snd) 1
  id-lip = isNonExpanding→isLipschitzWith1
    (M' .snd) (idfun M) (M' .snd) id-ne
    where
    id-ne : IsNonExpanding (M' .snd) (idfun M) (M' .snd)
    id-ne .IsNonExpanding.pres≈ x y ε = idfun _

mapIdentityWithᵣ :
  FMM.mapLipschitzWithᵣ 1 (idfun M) id-lip ≡ idfun RM.ℭ̂ᵣ
mapIdentityWithᵣ = funExt (RM.Elimℭ̂ᵣ-Prop.go e)
  where
  e : RM.Elimℭ̂ᵣ-Prop λ x →
    FMM.mapLipschitzWithᵣ 1 (idfun M) id-lip x ≡ x
  e .RM.Elimℭ̂ᵣ-Prop.ιA x =
    FMM.mapLipschitzWithᵣ-ι 1 (idfun M) id-lip x
  e .RM.Elimℭ̂ᵣ-Prop.limA x gx IH =
      FMM.mapLipschitzWithᵣ-lim 1 (idfun M) id-lip x gx
    ∙ PM.limCong _ _
        (FMM.mapLipschitzWithᵣ-mapWitness 1 (idfun M) id-lip x gx)
        gx (funExt IH)
  e .RM.Elimℭ̂ᵣ-Prop.isPropA x = RM.isSetℭ̂ᵣ _ _


-- Composition has the same form.  In particular, no equation between the
-- twice-scaled witness and the once-scaled witness is required.

compositeLipschitzWith : ∀ L R (f : M → N) (g : N → O)
  → IsLipschitzWith (M' .snd) f (N' .snd) L
  → IsLipschitzWith (N' .snd) g (O' .snd) R
  → IsLipschitzWith (M' .snd) (g ∘ f) (O' .snd) (R ·₊ L)
compositeLipschitzWith L R f g f-lip g-lip
  .IsLipschitzWith.pres≈ x y ε x≈y =
  PBaseO.subst≈ (g (f x)) (g (f y))
    (ℚ.·Assoc (fst R) (fst L) (fst ε))
    (g-lip .IsLipschitzWith.pres≈ (f x) (f y) (L ·₊ ε)
      (f-lip .IsLipschitzWith.pres≈ x y ε x≈y))

mapCompositionWithᵣ : ∀ L R (f : M → N) (g : N → O) f-lip g-lip →
  FMO.mapLipschitzWithᵣ (R ·₊ L) (g ∘ f)
      (compositeLipschitzWith L R f g f-lip g-lip)
    ≡
  FNO.mapLipschitzWithᵣ R g g-lip ∘
    FMN.mapLipschitzWithᵣ L f f-lip
mapCompositionWithᵣ L R f g f-lip g-lip =
  funExt (RM.Elimℭ̂ᵣ-Prop.go e)
  where
  map-f = FMN.mapLipschitzWithᵣ L f f-lip
  map-g = FNO.mapLipschitzWithᵣ R g g-lip
  map-gf = FMO.mapLipschitzWithᵣ (R ·₊ L) (g ∘ f)
    (compositeLipschitzWith L R f g f-lip g-lip)

  e : RM.Elimℭ̂ᵣ-Prop λ x → map-gf x ≡ map-g (map-f x)
  e .RM.Elimℭ̂ᵣ-Prop.ιA x =
      FMO.mapLipschitzWithᵣ-ι (R ·₊ L) (g ∘ f)
        (compositeLipschitzWith L R f g f-lip g-lip) x
    ∙ sym
        (cong map-g (FMN.mapLipschitzWithᵣ-ι L f f-lip x)
        ∙ FNO.mapLipschitzWithᵣ-ι R g g-lip (f x))
  e .RM.Elimℭ̂ᵣ-Prop.limA x gx IH =
      FMO.mapLipschitzWithᵣ-lim (R ·₊ L) (g ∘ f)
        (compositeLipschitzWith L R f g f-lip g-lip) x gx
    ∙ PO.limCong
        (map-gf ∘ x)
        (λ ε → map-g (map-f (x ε)))
        gf-witness g-after-f-witness (funExt IH)
    ∙ sym
        (cong map-g (FMN.mapLipschitzWithᵣ-lim L f f-lip x gx)
        ∙ FNO.mapLipschitzWithᵣ-lim R g g-lip
            (map-f ∘ x) f-witness)
    where
    f-witness : RN.ScaleWitness (map-f ∘ x)
    f-witness =
      FMN.mapLipschitzWithᵣ-mapWitness L f f-lip x gx

    gf-witness : RO.ScaleWitness (map-gf ∘ x)
    gf-witness =
      FMO.mapLipschitzWithᵣ-mapWitness (R ·₊ L) (g ∘ f)
        (compositeLipschitzWith L R f g f-lip g-lip) x gx

    g-after-f-witness :
      RO.ScaleWitness (λ ε → map-g (map-f (x ε)))
    g-after-f-witness =
      FNO.mapLipschitzWithᵣ-mapWitness R g g-lip
        (map-f ∘ x) f-witness
  e .RM.Elimℭ̂ᵣ-Prop.isPropA x = RO.isSetℭ̂ᵣ _ _

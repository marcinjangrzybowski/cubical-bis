open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Refined.Functor
  {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation as PT hiding (rec)

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Alternative.Refined
  as RefinedDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Refined.Properties
  as RefinedPropertiesDefinition

module Source = RefinedDefinition M'
module Target = RefinedDefinition N'
module SourceProperties = RefinedPropertiesDefinition M'
module TargetProperties = RefinedPropertiesDefinition N'

open PositiveRationals
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing

private
  M = M' .fst
  N = N' .fst
  module PTarget = PremetricStr (TargetProperties.ℭ̂ᵣPremetricSpace .snd)
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


scaleΓ : ℚ₊ → Γ → Γ
scaleΓ L g .Γ.γ ε = L ·₊ (g .Γ.γ ε)
scaleΓ L g .Γ.mon-γ ε δ ε<δ =
  ·MonoL< (fst (g .Γ.γ ε)) (fst (g .Γ.γ δ))
    (fst L) (snd L) (g .Γ.mon-γ ε δ ε<δ)
scaleΓ L g .Γ.τ ε = g .Γ.τ (ε ₊／₊ L)
scaleΓ L g .Γ.γ∘τ≤id ε = begin≤
  fst (L ·₊ g .Γ.γ (g .Γ.τ (ε ₊／₊ L)))
    ≤⟨ ·MonoL≤ _ _ (fst L)
      (OrderedCommRingStr.<-≤-weaken (snd ℚOrderedCommRing)
        0 (fst L) (snd L))
      (g .Γ.γ∘τ≤id (ε ₊／₊ L)) ⟩
  fst (L ·₊ (ε ₊／₊ L))
    ≡→≤⟨ ·／ L ε ⟩
  fst ε ◾


private
  scaleDifference : ∀ (L ε δ : ℚ₊) →
    fst L ℚ.· (fst ε ℚ.- fst δ) ≡
      (fst L ℚ.· fst ε) ℚ.- (fst L ℚ.· fst δ)
  scaleDifference L ε δ =
      ℚ.·DistL+ (fst L) (fst ε) (ℚ.- fst δ)
    ∙ cong (fst (L ·₊ ε) ℚ.+_) (ℚRing.-DistR· (fst L) (fst δ))

  scaleDifferenceSum : ∀ (L ε δ η : ℚ₊) →
    fst L ℚ.· (fst ε ℚ.- (fst δ ℚ.+ fst η)) ≡
      (fst L ℚ.· fst ε) ℚ.-
        ((fst L ℚ.· fst δ) ℚ.+ (fst L ℚ.· fst η))
  scaleDifferenceSum L ε δ η =
      scaleDifference L ε (δ +₊ η)
    ∙ cong (fst (L ·₊ ε) ℚ.+_)
        (cong ℚ.-_ (ℚ.·DistL+ (fst L) (fst δ) (fst η)))


module _ (L : ℚ₊) (f : M → N)
  (f-lip : IsLipschitzWith (M' .snd) f (N' .snd) L) where

  private
    scaledCauchy : ∀ (x : ℚ₊ → Target.ℭ̂ᵣ) (g : Γ) →
      (∀ ε δ → x ε Target.∼̂ᵣ[
        L ·₊ (g .Γ.γ ε +₊ g .Γ.γ δ) ] x δ) →
      ∀ ε δ → x ε Target.∼̂ᵣ[
        scaleΓ L g .Γ.γ ε +₊ scaleΓ L g .Γ.γ δ ] x δ
    scaledCauchy x g xc ε δ =
      PTarget.subst≈ (x ε) (x δ)
        (ℚ.·DistL+ (fst L)
          (fst (g .Γ.γ ε)) (fst (g .Γ.γ δ)))
        (xc ε δ)

    ScaledCauchy : (ℚ₊ → Target.ℭ̂ᵣ) → Γ → Type _
    ScaledCauchy x g = ∀ ε δ → x ε Target.∼̂ᵣ[
      L ·₊ (g .Γ.γ ε +₊ g .Γ.γ δ) ] x δ

    scaledWitness : ∀ (x : ℚ₊ → Target.ℭ̂ᵣ) →
      ∥ Σ Γ (ScaledCauchy x) ∥₁
      → Target.ScaleWitness x
    scaledWitness x = PT.map λ (g , xc) →
      scaleΓ L g , scaledCauchy x g xc

    rec : Source.Recℭ̂ᵣ Target.ℭ̂ᵣ
      (λ x y ε → x Target.∼̂ᵣ[ L ·₊ ε ] y)
    rec .Source.Recℭ̂ᵣ.ιA x = Target.ι (f x)
    rec .Source.Recℭ̂ᵣ.limA x gx = Target.lim x (scaledWitness x gx)
    rec .Source.Recℭ̂ᵣ.eqA x y x∼y =
      Target.eqℭ x y λ ε →
        PTarget.subst≈ x y (·／ L ε) (x∼y (ε ₊／₊ L))
    rec .Source.Recℭ̂ᵣ.ι-ι-B x y ε x≈y =
      Target.ι-ι (f x) (f y) (L ·₊ ε)
        (f-lip .IsLipschitzWith.pres≈ x y ε x≈y)
    rec .Source.Recℭ̂ᵣ.ι-lim-B x y g ε δ yc Δ inner =
      Target.ι-lim (f x) y (scaleΓ L g) (L ·₊ ε) δ
        (scaledCauchy y g yc) Δ' inner'
      where
      δ<ε : fst (g .Γ.γ δ) ℚ.< fst ε
      δ<ε = 0<Δ→< (fst (g .Γ.γ δ)) (fst ε) Δ

      Lδ<Lε : fst (L ·₊ g .Γ.γ δ) ℚ.< fst (L ·₊ ε)
      Lδ<Lε = ·MonoL< _ _ (fst L) (snd L) δ<ε

      Δ' : 0 ℚ.< (L ·₊ ε) -₊ (L ·₊ g .Γ.γ δ)
      Δ' = <→0<Δ _ _ Lδ<Lε

      inner' : Target.ι (f x) Target.∼̂ᵣ[
          ((L ·₊ ε) -₊ (L ·₊ g .Γ.γ δ) , Δ') ] y δ
      inner' = PTarget.subst≈ (Target.ι (f x)) (y δ)
        (scaleDifference L ε (g .Γ.γ δ)) inner
    rec .Source.Recℭ̂ᵣ.lim-ι-B x g y ε δ xc Δ inner =
      Target.lim-ι x (scaleΓ L g) (f y) (L ·₊ ε) δ
        (scaledCauchy x g xc) Δ' inner'
      where
      δ<ε : fst (g .Γ.γ δ) ℚ.< fst ε
      δ<ε = 0<Δ→< (fst (g .Γ.γ δ)) (fst ε) Δ

      Lδ<Lε : fst (L ·₊ g .Γ.γ δ) ℚ.< fst (L ·₊ ε)
      Lδ<Lε = ·MonoL< _ _ (fst L) (snd L) δ<ε

      Δ' : 0 ℚ.< (L ·₊ ε) -₊ (L ·₊ g .Γ.γ δ)
      Δ' = <→0<Δ _ _ Lδ<Lε

      inner' : x δ Target.∼̂ᵣ[
          ((L ·₊ ε) -₊ (L ·₊ g .Γ.γ δ) , Δ') ] Target.ι (f y)
      inner' = PTarget.subst≈ (x δ) (Target.ι (f y))
        (scaleDifference L ε (g .Γ.γ δ)) inner
    rec .Source.Recℭ̂ᵣ.lim-lim-B x g y g' ε δ η xc yc Δ inner =
      Target.lim-lim x (scaleΓ L g) y (scaleΓ L g')
        (L ·₊ ε) δ η (scaledCauchy x g xc) (scaledCauchy y g' yc)
        Δ' inner'
      where
      sum<ε : fst (g .Γ.γ δ +₊ g' .Γ.γ η) ℚ.< fst ε
      sum<ε = 0<Δ→< _ _ Δ

      scaledSum<scaledε :
        fst ((L ·₊ g .Γ.γ δ) +₊ (L ·₊ g' .Γ.γ η))
          ℚ.< fst (L ·₊ ε)
      scaledSum<scaledε = begin<
        fst ((L ·₊ g .Γ.γ δ) +₊ (L ·₊ g' .Γ.γ η))
          ≡→≤⟨ sym (ℚ.·DistL+ (fst L)
            (fst (g .Γ.γ δ)) (fst (g' .Γ.γ η))) ⟩
        fst (L ·₊ (g .Γ.γ δ +₊ g' .Γ.γ η))
          <⟨ ·MonoL< _ _ (fst L) (snd L) sum<ε ⟩
        fst (L ·₊ ε) ◾

      Δ' : 0 ℚ.< (L ·₊ ε) -₊
        ((L ·₊ g .Γ.γ δ) +₊ (L ·₊ g' .Γ.γ η))
      Δ' = <→0<Δ _ _ scaledSum<scaledε

      inner' : x δ Target.∼̂ᵣ[
          ((L ·₊ ε) -₊
            ((L ·₊ g .Γ.γ δ) +₊ (L ·₊ g' .Γ.γ η)) , Δ')
        ] y η
      inner' = PTarget.subst≈ (x δ) (y η)
        (scaleDifferenceSum L ε
          (g .Γ.γ δ) (g' .Γ.γ η)) inner
    rec .Source.Recℭ̂ᵣ.isPropB x y ε = Target.isProp∼ x (L ·₊ ε) y

  mapLipschitzWithᵣ : Source.ℭ̂ᵣ → Target.ℭ̂ᵣ
  mapLipschitzWithᵣ = Source.Recℭ̂ᵣ.go rec

  mapLipschitzWithᵣ-pres∼ : ∀ x y ε →
    x Source.∼̂ᵣ[ ε ] y →
    mapLipschitzWithᵣ x Target.∼̂ᵣ[ L ·₊ ε ] mapLipschitzWithᵣ y
  mapLipschitzWithᵣ-pres∼ x y ε = Source.Recℭ̂ᵣ.go∼ rec

  mapLipschitzWithᵣ-isLipschitz :
    IsLipschitzWith
      (SourceProperties.ℭ̂ᵣPremetricSpace .snd) mapLipschitzWithᵣ
      (TargetProperties.ℭ̂ᵣPremetricSpace .snd) L
  mapLipschitzWithᵣ-isLipschitz .IsLipschitzWith.pres≈ =
    mapLipschitzWithᵣ-pres∼

  mapLipschitzWithᵣ-ι : ∀ x →
    mapLipschitzWithᵣ (Source.ι x) ≡ Target.ι (f x)
  mapLipschitzWithᵣ-ι = Source.Recℭ̂ᵣ.β-go-ι rec

  mapLipschitzWithᵣ-mapWitness : ∀ x →
    Source.ScaleWitness x →
    Target.ScaleWitness (mapLipschitzWithᵣ ∘ x)
  mapLipschitzWithᵣ-mapWitness x gx =
    scaledWitness (mapLipschitzWithᵣ ∘ x)
      (Source.Recℭ̂ᵣ.mapWitness rec gx)

  mapLipschitzWithᵣ-lim : ∀ x gx →
    mapLipschitzWithᵣ (Source.lim x gx) ≡
      Target.lim (mapLipschitzWithᵣ ∘ x)
        (mapLipschitzWithᵣ-mapWitness x gx)
  mapLipschitzWithᵣ-lim = Source.Recℭ̂ᵣ.β-go-lim rec

  mapLipschitzWithᵣ-limAny : ∀ x gx gy →
    mapLipschitzWithᵣ (Source.lim x gx) ≡
      Target.lim (mapLipschitzWithᵣ ∘ x) gy
  mapLipschitzWithᵣ-limAny x gx gy =
      mapLipschitzWithᵣ-lim x gx
    ∙ TargetProperties.limWitnessIrrelevant _ _ gy


-- A distinctive benefit of the refined constructor: different constants and
-- different Lipschitz proofs give the same extension because the entire
-- ScaleWitness argument of every limit is a proposition.

mapLipschitzWithᵣ-independent : ∀ L K f fL fK →
  mapLipschitzWithᵣ L f fL ≡ mapLipschitzWithᵣ K f fK
mapLipschitzWithᵣ-independent L K f fL fK = funExt pointwise
  where
  pointwise : ∀ x →
    mapLipschitzWithᵣ L f fL x ≡ mapLipschitzWithᵣ K f fK x
  pointwise = Source.Elimℭ̂ᵣ-Prop.go e
    where
    e : Source.Elimℭ̂ᵣ-Prop λ x →
      mapLipschitzWithᵣ L f fL x ≡ mapLipschitzWithᵣ K f fK x
    e .Source.Elimℭ̂ᵣ-Prop.ιA x =
      mapLipschitzWithᵣ-ι L f fL x
      ∙ sym (mapLipschitzWithᵣ-ι K f fK x)
    e .Source.Elimℭ̂ᵣ-Prop.limA x gx IH =
        mapLipschitzWithᵣ-lim L f fL x gx
      ∙ TargetProperties.limCong _ _ _ _ (funExt IH)
      ∙ sym (mapLipschitzWithᵣ-lim K f fK x gx)
    e .Source.Elimℭ̂ᵣ-Prop.isPropA x = Target.isSetℭ̂ᵣ _ _


private
  mapRec : (f : M → N) →
    PT.Rec→Set
      {A = Σ[ L ∈ ℚ₊ ] IsLipschitzWith (M' .snd) f (N' .snd) L}
      (Source.ℭ̂ᵣ → Target.ℭ̂ᵣ)
  mapRec f .PT.Rec→Set.isSetB =
    isSetΠ λ _ → Target.isSetℭ̂ᵣ
  mapRec f .PT.Rec→Set.f (L , fL) =
    mapLipschitzWithᵣ L f fL
  mapRec f .PT.Rec→Set.fconst (L , fL) (K , fK) =
    mapLipschitzWithᵣ-independent L K f fL fK

mapLipschitzFunᵣ : L[ M' , N' ] → Source.ℭ̂ᵣ → Target.ℭ̂ᵣ
mapLipschitzFunᵣ F = PT.Rec→Set.go (mapRec (fst F)) (snd F)

mapLipschitzFunᵣ-β : ∀ f L fL →
  mapLipschitzFunᵣ (f , ∣ L , fL ∣₁) ≡
    mapLipschitzWithᵣ L f fL
mapLipschitzFunᵣ-β f L fL =
  PT.Rec→Set.β-go (mapRec f) (L , fL)

mapLipschitzFunᵣ-ι : ∀ F x →
  mapLipschitzFunᵣ F (Source.ι x) ≡ Target.ι (fst F x)
mapLipschitzFunᵣ-ι (f , fL) x =
  PT.elim
    (λ fL → Target.isSetℭ̂ᵣ
      (mapLipschitzFunᵣ (f , fL) (Source.ι x)) (Target.ι (f x)))
    (λ { (L , lip) →
        cong (λ h → h (Source.ι x)) (mapLipschitzFunᵣ-β f L lip)
      ∙ mapLipschitzWithᵣ-ι L f lip x }) fL

mapLipschitzᵣ :
  L[ M' , N' ] →
  L[ SourceProperties.ℭ̂ᵣPremetricSpace ,
      TargetProperties.ℭ̂ᵣPremetricSpace ]
mapLipschitzᵣ F .fst = mapLipschitzFunᵣ F
mapLipschitzᵣ (f , fL) .snd =
  PT.elim
    (λ fL → isPropIsLipschitz
      (SourceProperties.ℭ̂ᵣPremetricSpace .snd)
      (mapLipschitzFunᵣ (f , fL))
      (TargetProperties.ℭ̂ᵣPremetricSpace .snd))
    (λ { (L , lip) →
      ∣ L , subst
          (λ h → IsLipschitzWith
            (SourceProperties.ℭ̂ᵣPremetricSpace .snd) h
            (TargetProperties.ℭ̂ᵣPremetricSpace .snd) L)
          (sym (mapLipschitzFunᵣ-β f L lip))
          (mapLipschitzWithᵣ-isLipschitz L f lip)
      ∣₁ }) fL


mapNonExpandingᵣ :
  NE[ M' , N' ] →
  NE[ SourceProperties.ℭ̂ᵣPremetricSpace ,
      TargetProperties.ℭ̂ᵣPremetricSpace ]
mapNonExpandingᵣ F =
  mapLipschitzWithᵣ 1 (fst F) f-lip ,
  isLipschitzWith1→isNonExpanding
    (SourceProperties.ℭ̂ᵣPremetricSpace .snd)
    (mapLipschitzWithᵣ 1 (fst F) f-lip)
    (TargetProperties.ℭ̂ᵣPremetricSpace .snd)
    (mapLipschitzWithᵣ-isLipschitz 1 (fst F) f-lip)
  where
  f-lip : IsLipschitzWith (M' .snd) (fst F) (N' .snd) 1
  f-lip = isNonExpanding→isLipschitzWith1
    (M' .snd) (fst F) (N' .snd) (snd F)

mapNonExpandingᵣ-ι : ∀ F x →
  fst (mapNonExpandingᵣ F) (Source.ι x) ≡ Target.ι (fst F x)
mapNonExpandingᵣ-ι F x =
  mapLipschitzWithᵣ-ι 1 (fst F)
    (isNonExpanding→isLipschitzWith1
      (M' .snd) (fst F) (N' .snd) (snd F)) x

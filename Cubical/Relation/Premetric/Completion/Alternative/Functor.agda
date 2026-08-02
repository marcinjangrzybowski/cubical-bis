open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Functor
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

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Alternative as Alternative
import Cubical.Relation.Premetric.Completion.Alternative.Properties
  as AlternativeProperties

module Source = Alternative M'
module Target = Alternative N'
module SourceProperties = AlternativeProperties M'
module TargetProperties = AlternativeProperties N'

open PositiveRationals
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing

private
  M = M' .fst
  N = N' .fst
  module PM = PremetricStr (M' .snd)
  module PN = PremetricStr (N' .snd)
  module PTarget = PremetricStr (TargetProperties.ℭ̂PremetricSpace .snd)
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


-- Multiplying the scale of every source limit lets a Lipschitz map preserve
-- its family without reindexing it.  Division is needed only when the target
-- completion later observes that limit.

scaleΓ : ℚ₊ → Source.Γ → Target.Γ
scaleΓ L g .Target.Γ.γ ε = L ·₊ (g .Source.Γ.γ ε)
scaleΓ L g .Target.Γ.mon-γ ε δ ε<δ =
  ·MonoL< (fst (g .Source.Γ.γ ε)) (fst (g .Source.Γ.γ δ))
    (fst L) (snd L) (g .Source.Γ.mon-γ ε δ ε<δ)
scaleΓ L g .Target.Γ.τ ε = g .Source.Γ.τ (ε ₊／₊ L)
scaleΓ L g .Target.Γ.γ∘τ≤id ε = begin≤
  fst (L ·₊ g .Source.Γ.γ (g .Source.Γ.τ (ε ₊／₊ L)))
    ≤⟨ ·MonoL≤ _ _ (fst L)
      (OrderedCommRingStr.<-≤-weaken (snd ℚOrderedCommRing)
        0 (fst L) (snd L))
      (g .Source.Γ.γ∘τ≤id (ε ₊／₊ L)) ⟩
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
    scaledCauchy : ∀ (x : ℚ₊ → Target.ℭ̂) (g : Source.Γ) →
      (∀ ε δ → x ε PTarget.≈[
        L ·₊ (g .Source.Γ.γ ε +₊ g .Source.Γ.γ δ) ] x δ) →
      ∀ ε δ → x ε Target.∼̂[
        scaleΓ L g .Target.Γ.γ ε +₊ scaleΓ L g .Target.Γ.γ δ ] x δ
    scaledCauchy x g xc ε δ =
      PTarget.subst≈ (x ε) (x δ)
        (ℚ.·DistL+ (fst L)
          (fst (g .Source.Γ.γ ε)) (fst (g .Source.Γ.γ δ)))
        (xc ε δ)

    rec : Source.Recℭ̂Sym Target.ℭ̂
      (λ x y ε → x PTarget.≈[ L ·₊ ε ] y)
    rec .Source.Recℭ̂Sym.ιA x = Target.ι (f x)
    rec .Source.Recℭ̂Sym.limA x g xc =
      Target.lim x (scaleΓ L g) (scaledCauchy x g xc)
    rec .Source.Recℭ̂Sym.eqA x y x≈y =
      Target.eqℭ x y λ ε →
        PTarget.subst≈ x y (·／ L ε) (x≈y (ε ₊／₊ L))
    rec .Source.Recℭ̂Sym.ι-ι-B x y ε x≈y =
      Target.ι-ι (f x) (f y) (L ·₊ ε)
        (f-lip .IsLipschitzWith.pres≈ x y ε x≈y)
    rec .Source.Recℭ̂Sym.ι-lim-B x y g ε δ yc Δ inner =
      Target.ι-lim (f x) y (scaleΓ L g) (L ·₊ ε) δ
        (scaledCauchy y g yc) Δ' inner'
      where
      δ<ε : fst (g .Source.Γ.γ δ) ℚ.< fst ε
      δ<ε = 0<Δ→< (fst (g .Source.Γ.γ δ)) (fst ε) Δ

      Lδ<Lε : fst (L ·₊ g .Source.Γ.γ δ) ℚ.< fst (L ·₊ ε)
      Lδ<Lε = ·MonoL< _ _ (fst L) (snd L) δ<ε

      Δ' : 0 ℚ.< (L ·₊ ε) -₊ (L ·₊ g .Source.Γ.γ δ)
      Δ' = <→0<Δ _ _ Lδ<Lε

      inner' : Target.ι (f x) Target.∼̂[
          ((L ·₊ ε) -₊ (L ·₊ g .Source.Γ.γ δ) , Δ') ] y δ
      inner' = PTarget.subst≈ (Target.ι (f x)) (y δ)
        (scaleDifference L ε (g .Source.Γ.γ δ)) inner
    rec .Source.Recℭ̂Sym.lim-lim-B x g y g' ε δ η xc yc Δ inner =
      Target.lim-lim x (scaleΓ L g) y (scaleΓ L g')
        (L ·₊ ε) δ η (scaledCauchy x g xc) (scaledCauchy y g' yc)
        Δ' inner'
      where
      sum<ε : fst (g .Source.Γ.γ δ +₊ g' .Source.Γ.γ η) ℚ.< fst ε
      sum<ε = 0<Δ→< _ _ Δ

      scaledSum<scaledε :
        fst ((L ·₊ g .Source.Γ.γ δ) +₊ (L ·₊ g' .Source.Γ.γ η))
          ℚ.< fst (L ·₊ ε)
      scaledSum<scaledε = begin<
        fst ((L ·₊ g .Source.Γ.γ δ) +₊ (L ·₊ g' .Source.Γ.γ η))
          ≡→≤⟨ sym (ℚ.·DistL+ (fst L)
            (fst (g .Source.Γ.γ δ)) (fst (g' .Source.Γ.γ η))) ⟩
        fst (L ·₊ (g .Source.Γ.γ δ +₊ g' .Source.Γ.γ η))
          <⟨ ·MonoL< _ _ (fst L) (snd L) sum<ε ⟩
        fst (L ·₊ ε) ◾

      Δ' : 0 ℚ.< (L ·₊ ε) -₊
        ((L ·₊ g .Source.Γ.γ δ) +₊ (L ·₊ g' .Source.Γ.γ η))
      Δ' = <→0<Δ _ _ scaledSum<scaledε

      inner' : x δ Target.∼̂[
          ((L ·₊ ε) -₊
            ((L ·₊ g .Source.Γ.γ δ) +₊ (L ·₊ g' .Source.Γ.γ η)) , Δ')
        ] y η
      inner' = PTarget.subst≈ (x δ) (y η)
        (scaleDifferenceSum L ε
          (g .Source.Γ.γ δ) (g' .Source.Γ.γ η)) inner
    rec .Source.Recℭ̂Sym.isSymB x y ε =
      PTarget.isSym≈ x y (L ·₊ ε)
    rec .Source.Recℭ̂Sym.isPropB x y ε =
      PTarget.isProp≈ x y (L ·₊ ε)

  -- Unlike the usual completion lifting theorem, this map is defined only by
  -- the two HIT recursors.  The codomain needs no separate completeness proof.

  mapLipschitzWitĥ : Source.ℭ̂ → Target.ℭ̂
  mapLipschitzWitĥ = Source.Recℭ̂Sym.go rec

  mapLipschitzWitĥ-pres∼ : ∀ x y ε →
    x Source.∼̂[ ε ] y →
    mapLipschitzWitĥ x Target.∼̂[ L ·₊ ε ] mapLipschitzWitĥ y
  mapLipschitzWitĥ-pres∼ x y ε = Source.Recℭ̂Sym.go∼ rec

  mapLipschitzWitĥ-isLipschitz :
    IsLipschitzWith
      (SourceProperties.ℭ̂PremetricSpace .snd) mapLipschitzWitĥ
      (TargetProperties.ℭ̂PremetricSpace .snd) L
  mapLipschitzWitĥ-isLipschitz .IsLipschitzWith.pres≈ =
    mapLipschitzWitĥ-pres∼

  mapLipschitzWitĥ-ι : ∀ x →
    mapLipschitzWitĥ (Source.ι x) ≡ Target.ι (f x)
  mapLipschitzWitĥ-ι x = refl

  mapLipschitzWitĥ-lim : ∀ x g xc →
    mapLipschitzWitĥ (Source.lim x g xc) ≡
      Target.lim (mapLipschitzWitĥ ∘ x) (scaleΓ L g)
        (scaledCauchy (mapLipschitzWitĥ ∘ x) g
          (λ ε δ → mapLipschitzWitĥ-pres∼
            (x ε) (x δ) (g .Source.Γ.γ ε +₊ g .Source.Γ.γ δ) (xc ε δ)))
  mapLipschitzWitĥ-lim x g xc = refl


-- In particular, non-expanding maps act directly on alternative
-- completions.  This packaging requires no limit-preservation theorem.

mapNonExpandinĝ :
  NE[ M' , N' ] →
  NE[ SourceProperties.ℭ̂PremetricSpace ,
      TargetProperties.ℭ̂PremetricSpace ]
mapNonExpandinĝ F =
  mapLipschitzWitĥ 1 (fst F) f-lip ,
  isLipschitzWith1→isNonExpanding
    (SourceProperties.ℭ̂PremetricSpace .snd)
    (mapLipschitzWitĥ 1 (fst F) f-lip)
    (TargetProperties.ℭ̂PremetricSpace .snd)
    (mapLipschitzWitĥ-isLipschitz 1 (fst F) f-lip)
  where
  f-lip : IsLipschitzWith (M' .snd) (fst F) (N' .snd) 1
  f-lip = isNonExpanding→isLipschitzWith1
    (M' .snd) (fst F) (N' .snd) (snd F)

mapNonExpandinĝ-ι : ∀ F x →
  fst (mapNonExpandinĝ F) (Source.ι x) ≡ Target.ι (fst F x)
mapNonExpandinĝ-ι F x = refl

module Cubical.Relation.Premetric.Completion.Rationals.PointwiseContinuousExtension.LocallyUniformRepresentatives where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Rationals.Base as ℚ hiding (isProp∼)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Base
  as CompletionDefinition
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as CompletionPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Lift.PointwiseContinuousExtension
  as PointwiseExtensionDefinition

module R = CompletionDefinition ℚPremetricSpace
module RP = CompletionPropertiesDefinition ℚPremetricSpace
module E = PointwiseExtensionDefinition ℚPremetricSpace ℚPremetricSpace

private
  module Pℝ = PremetricStr (RP.ℭPremetricSpace .snd)

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing


-- Uniform continuity is required only when both arguments lie in the open
-- rho-neighbourhood of x.  The function remains total, but its values and
-- behaviour outside that neighbourhood are irrelevant.

record IsUniformlyContinuousOnNeighborhoodWith
  (F : R.ℭ → R.ℭ) (x : R.ℭ) (ρ : ℚ₊)
  (μ : ℚ₊ → ℚ₊) : Type₀ where
  field
    pres∼ : ∀ u v ε →
      u R.∼[ ρ ] x →
      v R.∼[ ρ ] x →
      u R.∼[ μ ε ] v →
      F u R.∼[ ε ] F v

open IsUniformlyContinuousOnNeighborhoodWith


UniformContinuityDataOnNeighborhood :
  (F : R.ℭ → R.ℭ) → R.ℭ → ℚ₊ → Type₀
UniformContinuityDataOnNeighborhood F x ρ =
  Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
    IsUniformlyContinuousOnNeighborhoodWith F x ρ μ


isUniformlyContinuousOnNeighborhood :
  (F : R.ℭ → R.ℭ) → R.ℭ → ℚ₊ → Type₀
isUniformlyContinuousOnNeighborhood F x ρ =
  ∥ UniformContinuityDataOnNeighborhood F x ρ ∥₁


isPropIsUniformlyContinuousOnNeighborhood : ∀ F x ρ →
  isProp (isUniformlyContinuousOnNeighborhood F x ρ)
isPropIsUniformlyContinuousOnNeighborhood F x ρ = squash₁


-- This is the proposed local-uniform presentation of a liftable rational
-- germ.  Different points may use unrelated functions, radii and moduli.

LocalUniformRepresentativeAt :
  (ℚ → R.ℭ) → R.ℭ → Type₀
LocalUniformRepresentativeAt f x =
  Σ[ F ∈ (R.ℭ → R.ℭ) ]
  Σ[ ρ ∈ ℚ₊ ]
    isUniformlyContinuousOnNeighborhood F x ρ
    ×
    (∀ q → R.ι q R.∼[ ρ ] x → F (R.ι q) ≡ f q)


IsMerelyLocallyUniformlyRepresentable :
  (ℚ → R.ℭ) → Type₀
IsMerelyLocallyUniformlyRepresentable f =
  ∀ x → ∥ LocalUniformRepresentativeAt f x ∥₁


-- For comparison, this is the property of one already defined real map.
-- Radius and modulus are chosen together under one truncation, as in the
-- usual constructive formulation of local uniform continuity.

IsLocallyUniformlyContinuous : (R.ℭ → R.ℭ) → Type₀
IsLocallyUniformlyContinuous F =
  ∀ x →
    ∥ Σ[ ρ ∈ ℚ₊ ]
      UniformContinuityDataOnNeighborhood F x ρ ∥₁


isPropIsLocallyUniformlyContinuous : ∀ F →
  isProp (IsLocallyUniformlyContinuous F)
isPropIsLocallyUniformlyContinuous F = isPropΠ λ _ → squash₁


locallyUniformlyContinuous→continuous : ∀ F →
  IsLocallyUniformlyContinuous F →
  isContinuous
    (RP.ℭPremetricSpace .snd) F
    (RP.ℭPremetricSpace .snd)
locallyUniformlyContinuous→continuous F F-local x
  .IsContinuousAt.pres≈ ε =
  PT.rec squash₁ withLocalData (F-local x)
  where
  withLocalData :
    ( Σ[ ρ ∈ ℚ₊ ]
      UniformContinuityDataOnNeighborhood F x ρ) →
    ∥ Σ[ θ ∈ ℚ₊ ]
      (∀ y → x R.∼[ θ ] y → F x R.∼[ ε ] F y) ∥₁
  withLocalData (ρ , μ , uniform) = ∣ θ , preserve ∣₁
    where
    θ = min₊ (μ ε) ρ /2₊

    preserve : ∀ y → x R.∼[ θ ] y → F x R.∼[ ε ] F y
    preserve y x∼y =
      uniform .pres∼ x y ε
        (Pℝ.isRefl≈ x ρ)
        (Pℝ.isMonotone≈< y x θ ρ
          (min/2₊<R (μ ε) ρ)
          (Pℝ.isSym≈ x y θ x∼y))
        (Pℝ.isMonotone≈< x y θ (μ ε)
          (min/2₊<L (μ ε) ρ) x∼y)


locallyUniformlyContinuousRestriction→locallyUniformRepresentative :
  ∀ F →
  IsLocallyUniformlyContinuous F →
  IsMerelyLocallyUniformlyRepresentable (F ∘ R.ι)
locallyUniformlyContinuousRestriction→locallyUniformRepresentative
  F F-local x =
  PT.map
    (λ ( ρ , μ , uniform ) →
      F , ρ , ∣ μ , uniform ∣₁ , λ q _ → refl)
    (F-local x)


-- Local uniform continuity at the pair (iota q,x) gives convergence to
-- F x.  Both the modulus and the representative may remain truncated.

localUniformRepresentative-tends : ∀ f x →
  (representative : LocalUniformRepresentativeAt f x) →
  E.TendsToAt f x (representative .fst x)
localUniformRepresentative-tends
  f x (F , ρ , F-uc , agrees) ε =
  PT.rec squash₁ withModulus F-uc
  where
  withModulus :
    UniformContinuityDataOnNeighborhood F x ρ →
    ∥ Σ[ θ ∈ ℚ₊ ]
      (∀ q → R.ι q R.∼[ θ ] x →
        f q R.∼[ ε ] F x) ∥₁
  withModulus (μ , uniform) = ∣ θ , preserve ∣₁
    where
    θ = min₊ (μ ε) ρ /2₊

    preserve : ∀ q → R.ι q R.∼[ θ ] x →
      f q R.∼[ ε ] F x
    preserve q ιq∼x =
      subst
        (λ z → z R.∼[ ε ] F x)
        (agrees q ιq-in-neighborhood)
        (uniform .pres∼ (R.ι q) x ε
          ιq-in-neighborhood
          (Pℝ.isRefl≈ x ρ)
          ιq-close-enough)
      where
      ιq-in-neighborhood : R.ι q R.∼[ ρ ] x
      ιq-in-neighborhood =
        Pℝ.isMonotone≈< (R.ι q) x θ ρ
          (min/2₊<R (μ ε) ρ) ιq∼x

      ιq-close-enough : R.ι q R.∼[ μ ε ] x
      ιq-close-enough =
        Pℝ.isMonotone≈< (R.ι q) x θ (μ ε)
          (min/2₊<L (μ ε) ρ) ιq∼x


merelyLocallyUniformlyRepresentable→everywhereConvergent : ∀ f →
  IsMerelyLocallyUniformlyRepresentable f →
  E.IsEverywhereConvergent f
merelyLocallyUniformlyRepresentable→everywhereConvergent f local x =
  PT.map
    (λ representative →
      representative .fst x ,
      localUniformRepresentative-tends f x representative)
    (local x)


-- A local representative determines not only the value at its centre.  Any
-- exact extension agrees with it on a smaller neighbourhood, because both
-- are limits of the same rational germ there.

localUniformRepresentative-tends-near :
  ∀ f x F ρ μ →
  IsUniformlyContinuousOnNeighborhoodWith F x ρ μ →
  (∀ q → R.ι q R.∼[ ρ ] x → F (R.ι q) ≡ f q) →
  ∀ y → y R.∼[ ρ /4₊ ] x →
  E.TendsToAt f y (F y)
localUniformRepresentative-tends-near
  f x F ρ μ uniform agrees y y∼x ε =
  ∣ sourceRadius , preserve ∣₁
  where
  sourceRadius = min₊ (μ ε) (ρ /4₊) /2₊

  sourcePlusCentre<ρ :
    (sourceRadius +₊ ρ /4₊) <₊ ρ
  sourcePlusCentre<ρ = begin<
    fst (sourceRadius +₊ ρ /4₊)
      <⟨ +MonoR< (fst sourceRadius) (fst (ρ /4₊))
          (fst (ρ /4₊)) (min/2₊<R (μ ε) (ρ /4₊)) ⟩
    fst (ρ /4₊ +₊ ρ /4₊)
      ≡→≤⟨ /4+/4≡/2 (fst ρ) ⟩
    fst (ρ /2₊)
      <⟨ /2₊<id ρ ⟩
    fst ρ ◾

  preserve : ∀ q → R.ι q R.∼[ sourceRadius ] y →
    f q R.∼[ ε ] F y
  preserve q ιq∼y =
    subst
      (λ z → z R.∼[ ε ] F y)
      (agrees q ιq-in-neighborhood)
      (uniform .pres∼ (R.ι q) y ε
        ιq-in-neighborhood y-in-neighborhood ιq-close-enough)
    where
    y-in-neighborhood : y R.∼[ ρ ] x
    y-in-neighborhood =
      Pℝ.isMonotone≈< y x (ρ /4₊) ρ (/4₊<id ρ) y∼x

    ιq-in-neighborhood : R.ι q R.∼[ ρ ] x
    ιq-in-neighborhood =
      Pℝ.isMonotone≈< (R.ι q) x
        (sourceRadius +₊ ρ /4₊) ρ sourcePlusCentre<ρ
        (Pℝ.isTriangular≈ (R.ι q) y x
          sourceRadius (ρ /4₊) ιq∼y y∼x)

    ιq-close-enough : R.ι q R.∼[ μ ε ] y
    ιq-close-enough =
      Pℝ.isMonotone≈< (R.ι q) y sourceRadius (μ ε)
        (min/2₊<L (μ ε) (ρ /4₊)) ιq∼y


localUniformRepresentatives→extensionLocallyUniformlyContinuous :
  ∀ f →
  IsMerelyLocallyUniformlyRepresentable f →
  (G : R.ℭ → R.ℭ) →
  (∀ y → E.TendsToAt f y (G y)) →
  IsLocallyUniformlyContinuous G
localUniformRepresentatives→extensionLocallyUniformlyContinuous
  f local G G-tends x =
  PT.rec squash₁ withRepresentative (local x)
  where
  withRepresentative :
    LocalUniformRepresentativeAt f x →
    ∥ Σ[ θ ∈ ℚ₊ ]
      UniformContinuityDataOnNeighborhood G x θ ∥₁
  withRepresentative (F , ρ , F-uc , agrees) =
    PT.map withModulus F-uc
    where
    withModulus :
      UniformContinuityDataOnNeighborhood F x ρ →
      Σ[ θ ∈ ℚ₊ ]
        UniformContinuityDataOnNeighborhood G x θ
    withModulus (μ , uniform) = ρ /4₊ , μ , G-uniform
      where
      agrees-near : ∀ y → y R.∼[ ρ /4₊ ] x → G y ≡ F y
      agrees-near y y∼x =
        E.tendsToAt-unique y (G y) (F y)
          (G-tends y)
          (localUniformRepresentative-tends-near
            f x F ρ μ uniform agrees y y∼x)

      G-uniform :
        IsUniformlyContinuousOnNeighborhoodWith G x (ρ /4₊) μ
      G-uniform .pres∼ u v ε u∼x v∼x u∼v =
        subst2 (λ a b → a R.∼[ ε ] b)
          (sym (agrees-near u u∼x))
          (sym (agrees-near v v∼x))
          (uniform .pres∼ u v ε
            (Pℝ.isMonotone≈< u x (ρ /4₊) ρ
              (/4₊<id ρ) u∼x)
            (Pℝ.isMonotone≈< v x (ρ /4₊) ρ
              (/4₊<id ρ) v∼x)
            u∼v)


LocallyUniformTendingExtension : (ℚ → R.ℭ) → Type₀
LocallyUniformTendingExtension f =
  Σ[ G ∈ (R.ℭ → R.ℭ) ]
    (∀ x → E.TendsToAt f x (G x))
    × IsLocallyUniformlyContinuous G


merelyLocallyUniformlyRepresentable→locallyUniformExtension : ∀ f →
  IsMerelyLocallyUniformlyRepresentable f →
  LocallyUniformTendingExtension f
merelyLocallyUniformlyRepresentable→locallyUniformExtension f local =
  G , G-tends ,
  localUniformRepresentatives→extensionLocallyUniformlyContinuous
    f local G G-tends
  where
  convergent : E.IsEverywhereConvergent f
  convergent =
    merelyLocallyUniformlyRepresentable→everywhereConvergent f local

  G : R.ℭ → R.ℭ
  G = E.liftEverywhereConvergent f convergent

  G-tends : ∀ x → E.TendsToAt f x (G x)
  G-tends = E.liftEverywhereConvergent-tends f convergent


-- Global uniform continuity and global Lipschitz continuity are immediate
-- ways of satisfying the neighbourhood part.

uniformlyContinuous→uniformlyContinuousOnNeighborhood :
  ∀ F x ρ →
  isUniformlyContinuous
    (RP.ℭPremetricSpace .snd) F
    (RP.ℭPremetricSpace .snd) →
  isUniformlyContinuousOnNeighborhood F x ρ
uniformlyContinuous→uniformlyContinuousOnNeighborhood F x ρ =
  PT.map λ ( μ , uniform ) → μ , local uniform
  where
  local : ∀ {μ} →
    IsUniformlyContinuousWith
      (RP.ℭPremetricSpace .snd) F
      (RP.ℭPremetricSpace .snd) μ →
    IsUniformlyContinuousOnNeighborhoodWith F x ρ μ
  local uniform .pres∼ u v ε _ _ =
    uniform .IsUniformlyContinuousWith.pres≈ u v ε


lipschitz→uniformlyContinuousOnNeighborhood :
  ∀ F x ρ →
  isLipschitz
    (RP.ℭPremetricSpace .snd) F
    (RP.ℭPremetricSpace .snd) →
  isUniformlyContinuousOnNeighborhood F x ρ
lipschitz→uniformlyContinuousOnNeighborhood F x ρ F-lip =
  uniformlyContinuous→uniformlyContinuousOnNeighborhood F x ρ
    (isLipschitz→isUniformlyContinuous
      (RP.ℭPremetricSpace .snd) F
      (RP.ℭPremetricSpace .snd) F-lip)

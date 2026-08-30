open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Lift.PointwiseContinuousExtension
  {ℓM} {ℓM'} {ℓN} {ℓN'}
  (M' : PremetricSpace ℓM ℓM')
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

import Cubical.Relation.Premetric.Completion.Base
  as CompletionDefinition
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as CompletionPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Properties.Approximations
  as ApproximationDefinition

module S = CompletionDefinition M'
module T = CompletionDefinition N'
module SP = CompletionPropertiesDefinition M'
module TP = CompletionPropertiesDefinition N'
module Approx = ApproximationDefinition.Show M'

private
  M = M' .fst
  ℓₘ = ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')
  module PS = PremetricStr (SP.ℭPremetricSpace .snd)
  module PT' = PremetricStr (TP.ℭPremetricSpace .snd)

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


-- The exact condition says directly that the dense germ of `f` has a limit
-- at every point of the native completion.

TendsToAt :
  (M → T.ℭ) → S.ℭ → T.ℭ → Type ℓₘ
TendsToAt f x y = ∀ ε →
  ∃[ δ ∈ ℚ₊ ]
    (∀ q → S.ι q S.∼[ δ ] x → f q T.∼[ ε ] y)


IsEverywhereConvergent : (M → T.ℭ) → Type ℓₘ
IsEverywhereConvergent f =
  ∀ x → ∃[ y ∈ T.ℭ ] TendsToAt f x y


isPropTendsToAt : ∀ f x y → isProp (TendsToAt f x y)
isPropTendsToAt f x y = isPropΠ λ _ → squash₁


isPropIsEverywhereConvergent : ∀ f →
  isProp (IsEverywhereConvergent f)
isPropIsEverywhereConvergent f = isPropΠ λ _ → squash₁


private
  twoQuarter< : ∀ ε → (ε /4₊ +₊ ε /4₊) <₊ ε
  twoQuarter< ε = begin<
    fst (ε /4₊ +₊ ε /4₊)
      ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
    fst (ε /2₊)
      <⟨ /2₊<id ε ⟩
    fst ε ◾


-- Limits of the same dense germ are unique.  The shared rational
-- approximation is obtained directly from Completion.Base density.

tendsToAt-unique :
  ∀ {f : M → T.ℭ} x y y' →
  TendsToAt f x y → TendsToAt f x y' →
  y ≡ y'
tendsToAt-unique {f} x y y' tends tends' =
  T.eqℭ y y' close
  where
  withRadii : ∀ {ε} →
    (Σ[ δ ∈ ℚ₊ ]
      (∀ q → S.ι q S.∼[ δ ] x →
        f q T.∼[ ε /4₊ ] y)) →
    (Σ[ η ∈ ℚ₊ ]
      (∀ q → S.ι q S.∼[ η ] x →
        f q T.∼[ ε /4₊ ] y')) →
    y T.∼[ ε ] y'

  close : ∀ ε → y T.∼[ ε ] y'
  close ε =
    PT.rec2 (T.isProp∼ y ε y') withRadii
      (tends (ε /4₊)) (tends' (ε /4₊))

  withRadii {ε} (δ , near) (η , near') =
    PT.rec (T.isProp∼ y ε y') withApproximation
      (Approx.∃approx x sourceRadius)
    where
    sourceRadius = min₊ δ η /2₊

    withApproximation :
      (Σ[ q ∈ M ] (S.ι q S.∼[ sourceRadius ] x)) →
      y T.∼[ ε ] y'
    withApproximation (q , ιq∼x) =
      PT'.isMonotone≈< y y' _ ε (twoQuarter< ε)
        (PT'.isTriangular≈ y (f q) y'
          (ε /4₊) (ε /4₊)
          (PT'.isSym≈ (f q) y (ε /4₊)
            (near q
              (PS.isMonotone≈< (S.ι q) x sourceRadius δ
                (min/2₊<L δ η) ιq∼x)))
          (near' q
            (PS.isMonotone≈< (S.ι q) x sourceRadius η
              (min/2₊<R δ η) ιq∼x)))


TendsToFiber : (M → T.ℭ) → S.ℭ → Type ℓₘ
TendsToFiber f x = Σ[ y ∈ T.ℭ ] TendsToAt f x y


isPropTendsToFiber : ∀ f x → isProp (TendsToFiber f x)
isPropTendsToFiber f x (y , tends) (y' , tends') =
  Σ≡Prop (isPropTendsToAt f x)
    (tendsToAt-unique x y y' tends tends')


-- Unique choice is now immediate: everywhere convergence already supplies
-- precisely the proposition-valued fiber needed to define the extension.

everywhereConvergentFiber :
  ∀ (f : M → T.ℭ) →
  IsEverywhereConvergent f →
  ∀ x → TendsToFiber f x
everywhereConvergentFiber f convergent x =
  PT.rec (isPropTendsToFiber f x) (λ fiber → fiber) (convergent x)


liftEverywhereConvergent :
  (f : M → T.ℭ) →
  IsEverywhereConvergent f →
  S.ℭ → T.ℭ
liftEverywhereConvergent f convergent x =
  everywhereConvergentFiber f convergent x .fst


liftEverywhereConvergent-tends :
  ∀ (f : M → T.ℭ) (convergent : IsEverywhereConvergent f) x →
  TendsToAt f x (liftEverywhereConvergent f convergent x)
liftEverywhereConvergent-tends f convergent x =
  everywhereConvergentFiber f convergent x .snd


-- Consequently, everywhere convergence is not merely a local regularity
-- hypothesis: it is equivalent to already having all values of an extension,
-- together with the assertion that they are the corresponding germ limits.

TendingExtension : (M → T.ℭ) → Type ℓₘ
TendingExtension f =
  Σ[ F ∈ (S.ℭ → T.ℭ) ]
    (∀ x → TendsToAt f x (F x))


isPropTendingExtension : ∀ f → isProp (TendingExtension f)
isPropTendingExtension f (F , tends) (G , tends') =
  Σ≡Prop
    (λ H → isPropΠ λ x → isPropTendsToAt f x (H x))
    (funExt λ x →
      tendsToAt-unique x (F x) (G x) (tends x) (tends' x))


everywhereConvergent≃tendingExtension : ∀ f →
  IsEverywhereConvergent f ≃ TendingExtension f
everywhereConvergent≃tendingExtension f =
  propBiimpl→Equiv
    (isPropIsEverywhereConvergent f)
    (isPropTendingExtension f)
    (λ convergent →
      liftEverywhereConvergent f convergent ,
      liftEverywhereConvergent-tends f convergent)
    (λ (F , tends) x → ∣ F x , tends x ∣₁)


-- At a base point, the germ limit equals the given value: insert that base
-- point itself into every radius supplied by convergence.

liftEverywhereConvergent-ι :
  ∀ f convergent q →
  liftEverywhereConvergent f convergent (S.ι q) ≡ f q
liftEverywhereConvergent-ι f convergent q =
  T.eqℭ (liftEverywhereConvergent f convergent (S.ι q)) (f q)
    λ ε → PT.rec
      (T.isProp∼
        (liftEverywhereConvergent f convergent (S.ι q)) ε (f q))
      (λ (δ , near) →
        PT'.isSym≈ (f q)
          (liftEverywhereConvergent f convergent (S.ι q)) ε
          (near q (PS.isRefl≈ (S.ι q) δ)))
      (liftEverywhereConvergent-tends f convergent (S.ι q) ε)


-- Direct continuity proof
-- -----------------------
--
-- For x close to y, choose a rational q close enough to y.  The same q is
-- also inside the convergence radius at x, so f q compares the two germ
-- limits.  No centered graph condition is introduced.

liftEverywhereConvergent-isContinuous :
  ∀ f (convergent : IsEverywhereConvergent f) →
  isContinuous
    (SP.ℭPremetricSpace .snd)
    (liftEverywhereConvergent f convergent)
    (TP.ℭPremetricSpace .snd)
liftEverywhereConvergent-isContinuous f convergent x
  .IsContinuousAt.pres≈ ε =
  PT.map withRadius
    (liftEverywhereConvergent-tends f convergent x (ε /4₊))
  where
  withRadius :
    (Σ[ δ ∈ ℚ₊ ]
      (∀ q → S.ι q S.∼[ δ ] x →
        f q T.∼[ ε /4₊ ] liftEverywhereConvergent f convergent x)) →
    Σ[ ρ ∈ ℚ₊ ]
      (∀ y → x S.∼[ ρ ] y →
        liftEverywhereConvergent f convergent x T.∼[ ε ]
          liftEverywhereConvergent f convergent y)
  withRadius (δ , nearX) = sourceRadius , preserve
    where
    sourceRadius = δ /4₊

    twiceSource<δ :
      (sourceRadius +₊ sourceRadius) <₊ δ
    twiceSource<δ = begin<
      fst (sourceRadius +₊ sourceRadius)
        ≡→≤⟨ /4+/4≡/2 (fst δ) ⟩
      fst (δ /2₊)
        <⟨ /2₊<id δ ⟩
      fst δ ◾

    preserve : ∀ y → x S.∼[ sourceRadius ] y →
      liftEverywhereConvergent f convergent x T.∼[ ε ]
        liftEverywhereConvergent f convergent y
    preserve y x∼y =
      PT.rec
        (T.isProp∼
          (liftEverywhereConvergent f convergent x) ε
          (liftEverywhereConvergent f convergent y))
        withYRadius
        (liftEverywhereConvergent-tends f convergent y (ε /4₊))
      where
      withYRadius :
        (Σ[ η ∈ ℚ₊ ]
          (∀ q → S.ι q S.∼[ η ] y →
            f q T.∼[ ε /4₊ ]
              liftEverywhereConvergent f convergent y)) →
        liftEverywhereConvergent f convergent x T.∼[ ε ]
          liftEverywhereConvergent f convergent y
      withYRadius (η , nearY) =
        PT.rec
          (T.isProp∼
            (liftEverywhereConvergent f convergent x) ε
            (liftEverywhereConvergent f convergent y))
          withApproximation
          (Approx.∃approx y approximationRadius)
        where
        approximationRadius = min₊ sourceRadius η /2₊

        approximationPlusSource<δ :
          (approximationRadius +₊ sourceRadius) <₊ δ
        approximationPlusSource<δ =
          ℚ.isTrans< _ _ _
            (+MonoR<
              (fst approximationRadius) (fst sourceRadius)
              (fst sourceRadius)
              (min/2₊<L sourceRadius η))
            twiceSource<δ

        withApproximation :
          (Σ[ q ∈ M ]
            (S.ι q S.∼[ approximationRadius ] y)) →
          liftEverywhereConvergent f convergent x T.∼[ ε ]
            liftEverywhereConvergent f convergent y
        withApproximation (q , ιq∼y) =
          PT'.isMonotone≈< _ _ _ ε (twoQuarter< ε)
            (PT'.isTriangular≈
              (liftEverywhereConvergent f convergent x) (f q)
              (liftEverywhereConvergent f convergent y)
              (ε /4₊) (ε /4₊)
              (PT'.isSym≈ (f q)
                (liftEverywhereConvergent f convergent x) (ε /4₊)
                (nearX q
                  (PS.isMonotone≈< (S.ι q) x
                    (approximationRadius +₊ sourceRadius) δ
                    approximationPlusSource<δ
                    (PS.isTriangular≈ (S.ι q) y x
                      approximationRadius sourceRadius ιq∼y
                      (PS.isSym≈ x y sourceRadius x∼y)))))
              (nearY q
                (PS.isMonotone≈< (S.ι q) y
                  approximationRadius η
                  (min/2₊<R sourceRadius η) ιq∼y)))


-- Conversely, ordinary continuity immediately says that the dense
-- restriction tends to F x at x.

continuousRestriction-tends :
  ∀ (F : S.ℭ → T.ℭ) →
  isContinuous
    (SP.ℭPremetricSpace .snd) F
    (TP.ℭPremetricSpace .snd) →
  ∀ x → TendsToAt (F ∘ S.ι) x (F x)
continuousRestriction-tends F F-cont x ε =
  PT.map withRadius (F-cont x .IsContinuousAt.pres≈ ε)
  where
  withRadius :
    (Σ[ δ ∈ ℚ₊ ]
      (∀ y → x S.∼[ δ ] y → F x T.∼[ ε ] F y)) →
    Σ[ δ ∈ ℚ₊ ]
      (∀ q → S.ι q S.∼[ δ ] x →
        F (S.ι q) T.∼[ ε ] F x)
  withRadius (δ , preserve) = δ , λ q ιq∼x →
    PT'.isSym≈ (F x) (F (S.ι q)) ε
      (preserve (S.ι q) (PS.isSym≈ (S.ι q) x δ ιq∼x))


continuous→everywhereConvergent :
  ∀ (F : S.ℭ → T.ℭ) →
  isContinuous
    (SP.ℭPremetricSpace .snd) F
    (TP.ℭPremetricSpace .snd) →
  IsEverywhereConvergent (F ∘ S.ι)
continuous→everywhereConvergent F F-cont x =
  ∣ F x , continuousRestriction-tends F F-cont x ∣₁


EverywhereConvergentRestriction : Type ℓₘ
EverywhereConvergentRestriction =
  Σ[ f ∈ (M → T.ℭ) ] IsEverywhereConvergent f


PointwiseContinuousMap : Type ℓₘ
PointwiseContinuousMap =
  Σ[ F ∈ (S.ℭ → T.ℭ) ]
    isContinuous
      (SP.ℭPremetricSpace .snd) F
      (TP.ℭPremetricSpace .snd)


extendEverywhereConvergent :
  EverywhereConvergentRestriction → PointwiseContinuousMap
extendEverywhereConvergent (f , convergent) =
  liftEverywhereConvergent f convergent ,
  liftEverywhereConvergent-isContinuous f convergent


restrictPointwiseContinuousMap :
  PointwiseContinuousMap → EverywhereConvergentRestriction
restrictPointwiseContinuousMap (F , F-cont) =
  F ∘ S.ι , continuous→everywhereConvergent F F-cont


restrictAfterExtend : ∀ restriction →
  restrictPointwiseContinuousMap
    (extendEverywhereConvergent restriction) ≡ restriction
restrictAfterExtend (f , convergent) =
  Σ≡Prop isPropIsEverywhereConvergent
    (funExt (liftEverywhereConvergent-ι f convergent))


extendAfterRestrict : ∀ continuous →
  extendEverywhereConvergent
    (restrictPointwiseContinuousMap continuous) ≡ continuous
extendAfterRestrict (F , F-cont) =
  Σ≡Prop
    (λ G → isPropIsContinuous
      (SP.ℭPremetricSpace .snd) G
      (TP.ℭPremetricSpace .snd))
    (funExt λ x →
      tendsToAt-unique x
        (liftEverywhereConvergent (F ∘ S.ι) restriction x)
        (F x)
        (liftEverywhereConvergent-tends
          (F ∘ S.ι) restriction x)
        (continuousRestriction-tends F F-cont x))
  where
  restriction = continuous→everywhereConvergent F F-cont


everywhereConvergentRestrictionMapIso :
  Iso EverywhereConvergentRestriction PointwiseContinuousMap
everywhereConvergentRestrictionMapIso = iso
  extendEverywhereConvergent
  restrictPointwiseContinuousMap
  extendAfterRestrict
  restrictAfterExtend


everywhereConvergentRestrictionMapEquiv :
  EverywhereConvergentRestriction ≃ PointwiseContinuousMap
everywhereConvergentRestrictionMapEquiv =
  isoToEquiv everywhereConvergentRestrictionMapIso

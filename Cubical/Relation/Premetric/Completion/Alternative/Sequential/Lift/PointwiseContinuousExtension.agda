open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.PointwiseContinuousExtension
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

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous
  as CauchyContinuousDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.PointwiseCompletionCentered
  as PointwiseDefinition

module S = SequentialDefinition M'
module SP = SequentialPropertiesDefinition M'
module T = SequentialDefinition N'
module TP = SequentialPropertiesDefinition N'
module C = CauchyContinuousDefinition M' N'
module P = PointwiseDefinition M' N'

private
  M = M' .fst
  ℓₘ = ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


-- The new ingredient is totality of the closure of the rational graph.
-- Existence remains truncated; pointwise centeredness will make each fiber
-- a proposition and therefore permit elimination of that truncation.

GraphFiber : (M → T.ℭ̂ₛ) → S.ℭ̂ₛ → Type ℓₘ
GraphFiber f x =
  Σ[ y ∈ T.ℭ̂ₛ ] C.JointlyApproximableFor f x y


IsMerelyGraphTotal : (M → T.ℭ̂ₛ) → Type ℓₘ
IsMerelyGraphTotal f = ∀ x → ∥ GraphFiber f x ∥₁


IsPointwiseContinuousRestriction :
  (M → T.ℭ̂ₛ) → Type ℓₘ
IsPointwiseContinuousRestriction f =
  P.IsPointwiseCompletionCenteredContinuous f ×
  IsMerelyGraphTotal f


private
  tripleQuarter< : ∀ ε →
    ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊) <₊ ε
  tripleQuarter< ε = begin<
    fst ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊)
      ≡→≤⟨ cong (ℚ._+ fst (ε /4₊)) (/4+/4≡/2 (fst ε)) ⟩
    fst (ε /2₊ +₊ ε /4₊)
      <⟨ +MonoL< (fst (ε /4₊)) (fst (ε /2₊))
           (fst (ε /2₊)) (/4₊</2₊ ε) ⟩
    fst (ε /2₊ +₊ ε /2₊)
      ≡→≤⟨ /2+/2≡id (fst ε) ⟩
    fst ε ◾


-- The pointwise centered condition is exactly what turns the graph relation
-- into a single-valued relation on completed inputs.

jointlyApproximable-unique :
  ∀ {f : M → T.ℭ̂ₛ} →
  P.IsPointwiseCompletionCenteredContinuous f →
  ∀ x y y' →
  C.JointlyApproximableFor f x y →
  C.JointlyApproximableFor f x y' →
  y ≡ y'
jointlyApproximable-unique {f} pointwise x y y' xy xy' =
  T.eqℭ y y' close
  where
  withRadius : ∀ {ε} →
    P.CenteredRadiusFor f x (ε /4₊) →
    y T.∼̂ₛ[ ε ] y'

  close : ∀ ε → y T.∼̂ₛ[ ε ] y'
  close ε =
    PT.rec (T.isProp∼ y ε y') withRadius
      (pointwise .P.IsPointwiseCompletionCenteredContinuous.at
        x (ε /4₊))

  withRadius {ε} (centerRadius , local) =
    PT.rec2 (T.isProp∼ y ε y') step
      (xy centerRadius (ε /4₊))
      (xy' centerRadius (ε /4₊))
    where
    step :
      (Σ[ q ∈ M ]
        (S.ι q S.∼̂ₛ[ centerRadius ] x) ×
        (f q T.∼̂ₛ[ ε /4₊ ] y)) →
      (Σ[ r ∈ M ]
        (S.ι r S.∼̂ₛ[ centerRadius ] x) ×
        (f r T.∼̂ₛ[ ε /4₊ ] y')) →
      y T.∼̂ₛ[ ε ] y'
    step (q , ιq∼x , fq∼y) (r , ιr∼x , fr∼y') =
      T.isMonotone∼̂ₛ< y y' _ ε (tripleQuarter< ε)
        (T.tri∼ y (f r) y'
          ((ε /4₊) +₊ (ε /4₊)) (ε /4₊)
          (T.tri∼ y (f q) (f r)
            (ε /4₊) (ε /4₊)
            (T.sym∼ (f q) y (ε /4₊) fq∼y)
            (local q r ιq∼x ιr∼x))
          fr∼y')


isPropGraphFiber :
  ∀ {f : M → T.ℭ̂ₛ} →
  P.IsPointwiseCompletionCenteredContinuous f →
  ∀ x → isProp (GraphFiber f x)
isPropGraphFiber {f} pointwise x (y , xy) (y' , xy') =
  Σ≡Prop (C.isPropJointlyApproximableFor f x)
    (jointlyApproximable-unique pointwise x y y' xy xy')


isPropIsPointwiseContinuousRestriction : ∀ f →
  isProp (IsPointwiseContinuousRestriction f)
isPropIsPointwiseContinuousRestriction f =
  isProp×
    (P.isPropIsPointwiseCompletionCenteredContinuous f)
    (isPropΠ λ _ → squash₁)


-- Unique choice now applies point by point: totality is truncated, but each
-- graph fiber is already a proposition.

pointwiseExtensionFiber :
  ∀ (f : M → T.ℭ̂ₛ)
    (restriction : IsPointwiseContinuousRestriction f) x →
  GraphFiber f x
pointwiseExtensionFiber f (pointwise , total) x =
  PT.rec (isPropGraphFiber pointwise x) (λ fiber → fiber) (total x)


liftPointwiseContinuousRestriction :
  (f : M → T.ℭ̂ₛ) →
  IsPointwiseContinuousRestriction f →
  S.ℭ̂ₛ → T.ℭ̂ₛ
liftPointwiseContinuousRestriction f restriction x =
  pointwiseExtensionFiber f restriction x .fst


liftPointwiseContinuousRestriction-joint :
  ∀ (f : M → T.ℭ̂ₛ)
    (restriction : IsPointwiseContinuousRestriction f) x →
  C.JointlyApproximableFor f x
    (liftPointwiseContinuousRestriction f restriction x)
liftPointwiseContinuousRestriction-joint f restriction x =
  pointwiseExtensionFiber f restriction x .snd


private
  exactBaseFiber : ∀ f q → GraphFiber f (S.ι q)
  exactBaseFiber f q =
    f q , λ α β →
      ∣ q , S.isRefl∼̂ₛ (S.ι q) α
          , T.isRefl∼̂ₛ (f q) β ∣₁


liftPointwiseContinuousRestriction-ι :
  ∀ f restriction q →
  liftPointwiseContinuousRestriction f restriction (S.ι q) ≡ f q
liftPointwiseContinuousRestriction-ι f (pointwise , total) q =
  cong fst
    (isPropGraphFiber pointwise (S.ι q)
      (pointwiseExtensionFiber f (pointwise , total) (S.ι q))
      (exactBaseFiber f q))


liftPointwiseContinuousRestriction-isContinuous :
  ∀ f restriction →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    (liftPointwiseContinuousRestriction f restriction)
    (TP.ℭ̂ₛPremetricSpace .snd)
liftPointwiseContinuousRestriction-isContinuous
  f restriction@(pointwise , _) =
  P.jointlyApproximableExtension-isContinuous f
    (liftPointwiseContinuousRestriction f restriction)
    pointwise
    (liftPointwiseContinuousRestriction-joint f restriction)


-- Conversely, ordinary continuity of a completed map makes its dense
-- restriction pointwise centered and makes the original value at each point
-- an inhabitant of the corresponding completed graph fiber.

continuousRestriction-joint :
  ∀ (F : S.ℭ̂ₛ → T.ℭ̂ₛ) →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd) F
    (TP.ℭ̂ₛPremetricSpace .snd) →
  ∀ x → C.JointlyApproximableFor (F ∘ S.ι) x (F x)
continuousRestriction-joint F F-cont x α β =
  PT.rec squash₁ withRadius
    (F-cont x .IsContinuousAt.pres≈ β)
  where
  withRadius :
    (Σ[ δ ∈ ℚ₊ ]
      (∀ z → x S.∼̂ₛ[ δ ] z → F x T.∼̂ₛ[ β ] F z)) →
    ∃[ q ∈ M ]
      (S.ι q S.∼̂ₛ[ α ] x) ×
      (F (S.ι q) T.∼̂ₛ[ β ] F x)
  withRadius (δ , preserve) =
    PT.map withApproximation
      (SP.∃approx x (min₊ α δ /2₊))
    where
    sourceRadius = min₊ α δ /2₊

    withApproximation :
      (Σ[ q ∈ M ] (S.ι q S.∼̂ₛ[ sourceRadius ] x)) →
      Σ[ q ∈ M ]
        (S.ι q S.∼̂ₛ[ α ] x) ×
        (F (S.ι q) T.∼̂ₛ[ β ] F x)
    withApproximation (q , ιq∼x) = q ,
      S.isMonotone∼̂ₛ< (S.ι q) x sourceRadius α
        (min/2₊<L α δ) ιq∼x ,
      T.sym∼ (F x) (F (S.ι q)) β
        (preserve (S.ι q)
          (S.isMonotone∼̂ₛ< x (S.ι q) sourceRadius δ
            (min/2₊<R α δ)
            (S.sym∼ (S.ι q) x sourceRadius ιq∼x)))


continuous→pointwiseContinuousRestriction :
  ∀ (F : S.ℭ̂ₛ → T.ℭ̂ₛ) →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd) F
    (TP.ℭ̂ₛPremetricSpace .snd) →
  IsPointwiseContinuousRestriction (F ∘ S.ι)
continuous→pointwiseContinuousRestriction F F-cont =
  P.continuous→pointwiseRestriction F F-cont ,
  λ x → ∣ F x , continuousRestriction-joint F F-cont x ∣₁


-- A single-condition formulation
-- ------------------------------
--
-- Instead of separately saying that the completed graph is locally
-- single-valued and merely total, say directly that the rational germ of f
-- has a limit at every completed input.

TendsToAt :
  (M → T.ℭ̂ₛ) → S.ℭ̂ₛ → T.ℭ̂ₛ → Type ℓₘ
TendsToAt f x y = ∀ ε →
  ∃[ δ ∈ ℚ₊ ]
    (∀ q → S.ι q S.∼̂ₛ[ δ ] x → f q T.∼̂ₛ[ ε ] y)


IsEverywhereConvergent : (M → T.ℭ̂ₛ) → Type ℓₘ
IsEverywhereConvergent f =
  ∀ x → ∃[ y ∈ T.ℭ̂ₛ ] TendsToAt f x y


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


tendsToAt-unique :
  ∀ {f : M → T.ℭ̂ₛ} x y y' →
  TendsToAt f x y → TendsToAt f x y' →
  y ≡ y'
tendsToAt-unique {f} x y y' tends tends' =
  T.eqℭ y y' close
  where
  withRadii : ∀ {ε} →
    (Σ[ δ ∈ ℚ₊ ]
      (∀ q → S.ι q S.∼̂ₛ[ δ ] x →
        f q T.∼̂ₛ[ ε /4₊ ] y)) →
    (Σ[ η ∈ ℚ₊ ]
      (∀ q → S.ι q S.∼̂ₛ[ η ] x →
        f q T.∼̂ₛ[ ε /4₊ ] y')) →
    y T.∼̂ₛ[ ε ] y'

  close : ∀ ε → y T.∼̂ₛ[ ε ] y'
  close ε =
    PT.rec2 (T.isProp∼ y ε y') withRadii
      (tends (ε /4₊)) (tends' (ε /4₊))

  withRadii {ε} (δ , near) (η , near') =
    PT.rec (T.isProp∼ y ε y') withApproximation
      (SP.∃approx x sourceRadius)
    where
    sourceRadius = min₊ δ η /2₊

    withApproximation :
      (Σ[ q ∈ M ] (S.ι q S.∼̂ₛ[ sourceRadius ] x)) →
      y T.∼̂ₛ[ ε ] y'
    withApproximation (q , ιq∼x) =
      T.isMonotone∼̂ₛ< y y' _ ε (twoQuarter< ε)
        (T.tri∼ y (f q) y' (ε /4₊) (ε /4₊)
          (T.sym∼ (f q) y (ε /4₊)
            (near q
              (S.isMonotone∼̂ₛ< (S.ι q) x sourceRadius δ
                (min/2₊<L δ η) ιq∼x)))
          (near' q
            (S.isMonotone∼̂ₛ< (S.ι q) x sourceRadius η
              (min/2₊<R δ η) ιq∼x)))


isPropTendsToFiber : ∀ f x →
  isProp (Σ[ y ∈ T.ℭ̂ₛ ] TendsToAt f x y)
isPropTendsToFiber f x (y , tends) (y' , tends') =
  Σ≡Prop (isPropTendsToAt f x)
    (tendsToAt-unique x y y' tends tends')


tendsToAt→jointlyApproximable :
  ∀ {f : M → T.ℭ̂ₛ} {x y} →
  TendsToAt f x y → C.JointlyApproximableFor f x y
tendsToAt→jointlyApproximable {f} {x} {y} tends α β =
  PT.rec squash₁ withRadius (tends β)
  where
  withRadius :
    (Σ[ δ ∈ ℚ₊ ]
      (∀ q → S.ι q S.∼̂ₛ[ δ ] x → f q T.∼̂ₛ[ β ] y)) →
    ∃[ q ∈ M ]
      (S.ι q S.∼̂ₛ[ α ] x) ×
      (f q T.∼̂ₛ[ β ] y)
  withRadius (δ , near) =
    PT.map withApproximation
      (SP.∃approx x (min₊ α δ /2₊))
    where
    sourceRadius = min₊ α δ /2₊

    withApproximation :
      (Σ[ q ∈ M ] (S.ι q S.∼̂ₛ[ sourceRadius ] x)) →
      Σ[ q ∈ M ]
        (S.ι q S.∼̂ₛ[ α ] x) ×
        (f q T.∼̂ₛ[ β ] y)
    withApproximation (q , ιq∼x) = q ,
      S.isMonotone∼̂ₛ< (S.ι q) x sourceRadius α
        (min/2₊<L α δ) ιq∼x ,
      near q
        (S.isMonotone∼̂ₛ< (S.ι q) x sourceRadius δ
          (min/2₊<R α δ) ιq∼x)


pointwiseJoint→tendsToAt :
  ∀ {f : M → T.ℭ̂ₛ} →
  P.IsPointwiseCompletionCenteredContinuous f →
  ∀ {x y} → C.JointlyApproximableFor f x y →
  TendsToAt f x y
pointwiseJoint→tendsToAt {f} pointwise {x} {y} joint ε =
  PT.rec squash₁ withCentered
    (pointwise .P.IsPointwiseCompletionCenteredContinuous.at
      x (ε /2₊))
  where
  withCentered :
    P.CenteredRadiusFor f x (ε /2₊) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ q → S.ι q S.∼̂ₛ[ δ ] x → f q T.∼̂ₛ[ ε ] y)
  withCentered (centerRadius , local) =
    PT.map withAnchor
      (joint (centerRadius /2₊) (ε /2₊))
    where
    sourceRadius = centerRadius /2₊

    withAnchor :
      (Σ[ r ∈ M ]
        (S.ι r S.∼̂ₛ[ sourceRadius ] x) ×
        (f r T.∼̂ₛ[ ε /2₊ ] y)) →
      Σ[ δ ∈ ℚ₊ ]
        (∀ q → S.ι q S.∼̂ₛ[ δ ] x → f q T.∼̂ₛ[ ε ] y)
    withAnchor (r , ιr∼x , fr∼y) =
      sourceRadius , λ q ιq∼x →
        subst (f q T.∼̂ₛ[_] y)
          (ℚ₊≡ (/2+/2≡id (fst ε)))
          (T.tri∼ (f q) (f r) y (ε /2₊) (ε /2₊)
            (local q r
              (S.isMonotone∼̂ₛ< (S.ι q) x
                sourceRadius centerRadius
                (/2₊<id centerRadius) ιq∼x)
              (S.isMonotone∼̂ₛ< (S.ι r) x
                sourceRadius centerRadius
                (/2₊<id centerRadius) ιr∼x))
            fr∼y)


everywhereConvergent→pointwiseCentered :
  ∀ {f : M → T.ℭ̂ₛ} →
  IsEverywhereConvergent f →
  P.IsPointwiseCompletionCenteredContinuous f
everywhereConvergent→pointwiseCentered {f} convergent
  .P.IsPointwiseCompletionCenteredContinuous.at x ε =
  PT.rec squash₁ withLimit (convergent x)
  where
  withLimit :
    (Σ[ y ∈ T.ℭ̂ₛ ] TendsToAt f x y) →
    ∥ P.CenteredRadiusFor f x ε ∥₁
  withLimit (y , tends) =
    PT.map withRadius (tends (ε /2₊))
    where
    withRadius :
      (Σ[ δ ∈ ℚ₊ ]
        (∀ q → S.ι q S.∼̂ₛ[ δ ] x →
          f q T.∼̂ₛ[ ε /2₊ ] y)) →
      P.CenteredRadiusFor f x ε
    withRadius (δ , near) = δ , λ q r ιq∼x ιr∼x →
      subst (f q T.∼̂ₛ[_] f r)
        (ℚ₊≡ (/2+/2≡id (fst ε)))
        (T.tri∼ (f q) y (f r) (ε /2₊) (ε /2₊)
          (near q ιq∼x)
          (T.sym∼ (f r) y (ε /2₊) (near r ιr∼x)))


everywhereConvergent→pointwiseContinuousRestriction :
  ∀ {f : M → T.ℭ̂ₛ} →
  IsEverywhereConvergent f →
  IsPointwiseContinuousRestriction f
everywhereConvergent→pointwiseContinuousRestriction
  {f} convergent =
  everywhereConvergent→pointwiseCentered convergent ,
  λ x → PT.map
    (λ (y , tends) → y , tendsToAt→jointlyApproximable tends)
    (convergent x)


pointwiseContinuousRestriction→everywhereConvergent :
  ∀ {f : M → T.ℭ̂ₛ} →
  IsPointwiseContinuousRestriction f →
  IsEverywhereConvergent f
pointwiseContinuousRestriction→everywhereConvergent
  (pointwise , total) x =
  PT.map
    (λ (y , joint) → y , pointwiseJoint→tendsToAt pointwise joint)
    (total x)


everywhereConvergent≃pointwiseContinuousRestriction : ∀ f →
  IsEverywhereConvergent f ≃ IsPointwiseContinuousRestriction f
everywhereConvergent≃pointwiseContinuousRestriction f =
  propBiimpl→Equiv
    (isPropIsEverywhereConvergent f)
    (isPropIsPointwiseContinuousRestriction f)
    everywhereConvergent→pointwiseContinuousRestriction
    pointwiseContinuousRestriction→everywhereConvergent


-- Exact classification: pointwise-continuous maps between the completions
-- are equivalent to dense restrictions whose graph is pointwise centered
-- and merely total.

PointwiseContinuousRestriction : Type ℓₘ
PointwiseContinuousRestriction =
  Σ[ f ∈ (M → T.ℭ̂ₛ) ] IsPointwiseContinuousRestriction f


PointwiseContinuousMap : Type ℓₘ
PointwiseContinuousMap =
  Σ[ F ∈ (S.ℭ̂ₛ → T.ℭ̂ₛ) ]
    isContinuous
      (SP.ℭ̂ₛPremetricSpace .snd) F
      (TP.ℭ̂ₛPremetricSpace .snd)


EverywhereConvergentRestriction : Type ℓₘ
EverywhereConvergentRestriction =
  Σ[ f ∈ (M → T.ℭ̂ₛ) ] IsEverywhereConvergent f


everywhereConvergentRestriction≃pointwiseContinuousRestriction :
  EverywhereConvergentRestriction ≃ PointwiseContinuousRestriction
everywhereConvergentRestriction≃pointwiseContinuousRestriction =
  Σ-cong-equiv-snd everywhereConvergent≃pointwiseContinuousRestriction


extendPointwiseContinuousRestriction :
  PointwiseContinuousRestriction → PointwiseContinuousMap
extendPointwiseContinuousRestriction (f , restriction) =
  liftPointwiseContinuousRestriction f restriction ,
  liftPointwiseContinuousRestriction-isContinuous f restriction


restrictPointwiseContinuousMap :
  PointwiseContinuousMap → PointwiseContinuousRestriction
restrictPointwiseContinuousMap (F , F-cont) =
  F ∘ S.ι , continuous→pointwiseContinuousRestriction F F-cont


restrictAfterExtendPointwiseContinuous :
  ∀ restriction →
  restrictPointwiseContinuousMap
    (extendPointwiseContinuousRestriction restriction) ≡ restriction
restrictAfterExtendPointwiseContinuous (f , restriction) =
  Σ≡Prop isPropIsPointwiseContinuousRestriction
    (funExt (liftPointwiseContinuousRestriction-ι f restriction))


extendAfterRestrictPointwiseContinuous :
  ∀ continuous →
  extendPointwiseContinuousRestriction
    (restrictPointwiseContinuousMap continuous) ≡ continuous
extendAfterRestrictPointwiseContinuous (F , F-cont) =
  Σ≡Prop
    (λ G → isPropIsContinuous
      (SP.ℭ̂ₛPremetricSpace .snd) G
      (TP.ℭ̂ₛPremetricSpace .snd))
    (funExt λ x →
      jointlyApproximable-unique restriction-pointwise x
        (liftPointwiseContinuousRestriction
          (F ∘ S.ι) restriction x)
        (F x)
        (liftPointwiseContinuousRestriction-joint
          (F ∘ S.ι) restriction x)
        (continuousRestriction-joint F F-cont x))
  where
  restriction = continuous→pointwiseContinuousRestriction F F-cont
  restriction-pointwise = fst restriction


pointwiseContinuousRestrictionMapIso :
  Iso PointwiseContinuousRestriction PointwiseContinuousMap
pointwiseContinuousRestrictionMapIso .Iso.fun =
  extendPointwiseContinuousRestriction
pointwiseContinuousRestrictionMapIso .Iso.inv =
  restrictPointwiseContinuousMap
pointwiseContinuousRestrictionMapIso .Iso.sec =
  extendAfterRestrictPointwiseContinuous
pointwiseContinuousRestrictionMapIso .Iso.ret =
  restrictAfterExtendPointwiseContinuous


pointwiseContinuousRestrictionMapEquiv :
  PointwiseContinuousRestriction ≃ PointwiseContinuousMap
pointwiseContinuousRestrictionMapEquiv =
  isoToEquiv pointwiseContinuousRestrictionMapIso


everywhereConvergentRestrictionMapEquiv :
  EverywhereConvergentRestriction ≃ PointwiseContinuousMap
everywhereConvergentRestrictionMapEquiv =
  everywhereConvergentRestriction≃pointwiseContinuousRestriction
  ∙ₑ pointwiseContinuousRestrictionMapEquiv

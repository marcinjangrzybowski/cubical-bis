module Cubical.HITs.CauchyRealsP.Analysis.Metric.Radius where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Clamp
open import Cubical.HITs.CauchyRealsP.Analysis.Metric.Interval

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace

ClosedAbsRadiusPredicate : ℝ → ℙ ℝ
ClosedAbsRadiusPredicate radius x =
  (absℝ x ≤ℝ radius)
  , isProp≤ℝ (absℝ x) radius

OpenAbsRadiusPredicate : ℝ → ℙ ℝ
OpenAbsRadiusPredicate radius =
  predicatePreimage absℝ (UpperOpenHalfLinePredicate radius)

ClosedAbsRadius : ℝ → Type
ClosedAbsRadius radius =
  Σ[ x ∈ ℝ ] x ∈ ClosedAbsRadiusPredicate radius

ClosedAbsRadiusPremetricSpace :
  ℝ → PremetricSpace ℓ-zero ℓ-zero
ClosedAbsRadiusPremetricSpace radius =
  PremetricSubspace
    ℝPremetricSpace
    (ClosedAbsRadiusPredicate radius)

closedAbsRadiusInclusionNE : ∀ radius →
  NE[ ClosedAbsRadiusPremetricSpace radius , ℝPremetricSpace ]
closedAbsRadiusInclusionNE radius =
  subspaceInclusionNE ℝPremetricSpace (ClosedAbsRadiusPredicate radius)

closedAbsRadiusRetractionNE : ∀ radius →
  0 ≤ℝ radius →
  NE[ ℝPremetricSpace , ClosedAbsRadiusPremetricSpace radius ]
fst (closedAbsRadiusRetractionNE radius 0≤radius) x =
  clampInterval (- radius) radius x
  , clampSymmetricAbsBound radius 0≤radius x
IsNonExpanding.pres≈
  (snd (closedAbsRadiusRetractionNE radius 0≤radius))
  x y ε x∼y =
    clampIntervalPres∼ (- radius) radius x y ε x∼y

closedAbsRadiusRetractionSection : ∀ radius →
  (0≤radius : 0 ≤ℝ radius) →
  ∀ point →
  fst (closedAbsRadiusRetractionNE radius 0≤radius)
      (fst (closedAbsRadiusInclusionNE radius) point)
    ≡ point
closedAbsRadiusRetractionSection radius 0≤radius point =
  Σ≡Prop
    (λ x → isProp≤ℝ (absℝ x) radius)
    (clampSymmetricFixpointFromAbs radius (fst point) (snd point))

closedAbsRadiusCoordinateIsContinuous :
  ∀ radius →
  isContinuous
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (snd ℝPremetricSpace)
closedAbsRadiusCoordinateIsContinuous
  radius point .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ point∼other → point∼other
      )

openAbsRadiusIsOpen : ∀ radius →
  IsOpenPredicate
    (snd ℝPremetricSpace)
    (OpenAbsRadiusPredicate radius)
openAbsRadiusIsOpen radius =
  continuousPreimageIsOpen
    absℝ
    (UpperOpenHalfLinePredicate radius)
    (snd (NE→C (absℝ , absIsNonExpanding)))
    (upperOpenHalfLineIsOpen radius)

openAbsRadius⊆closedAbsRadius : ∀ radius →
  OpenAbsRadiusPredicate radius ⊆ ClosedAbsRadiusPredicate radius
openAbsRadius⊆closedAbsRadius radius x interior =
  <ℝ-weaken (absℝ x) radius interior

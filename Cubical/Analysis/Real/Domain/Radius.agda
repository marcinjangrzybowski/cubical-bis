module Cubical.Analysis.Real.Domain.Radius where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Completeness
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Domain.Interval

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Instances.Subspace


ClosedAbsRadiusPredicate : ℝ → ℙ ℝ
ClosedAbsRadiusPredicate radius x =
  (absℝ x ≤ℝ radius)
  , isProp≤ℝ (absℝ x) radius

isPropClosedAbsRadiusMembership : ∀ radius x →
  isProp (x ∈ ClosedAbsRadiusPredicate radius)
isPropClosedAbsRadiusMembership radius x =
  isProp≤ℝ (absℝ x) radius

ClosedAbsRadius : ℝ → Type₀
ClosedAbsRadius radius =
  Σ[ x ∈ ℝ ] x ∈ ClosedAbsRadiusPredicate radius

isSetClosedAbsRadius : ∀ radius → isSet (ClosedAbsRadius radius)
isSetClosedAbsRadius radius =
  isSetΣSndProp isSetℝ (isPropClosedAbsRadiusMembership radius)

ClosedAbsRadiusPremetricSpace :
  ℝ → PremetricSpace ℓ-zero ℓ-zero
ClosedAbsRadiusPremetricSpace radius =
  PremetricSubspace ℝPremetricSpace (ClosedAbsRadiusPredicate radius)


closedAbsRadiusInclusionNE : ∀ radius →
  NE[ ClosedAbsRadiusPremetricSpace radius , ℝPremetricSpace ]
closedAbsRadiusInclusionNE radius =
  subspaceInclusionNE ℝPremetricSpace (ClosedAbsRadiusPredicate radius)

closedAbsRadiusInclusionUC : ∀ radius →
  UC[ ClosedAbsRadiusPremetricSpace radius , ℝPremetricSpace ]
closedAbsRadiusInclusionUC radius =
  NE→UC (closedAbsRadiusInclusionNE radius)

closedAbsRadiusInclusionC : ∀ radius →
  C[ ClosedAbsRadiusPremetricSpace radius , ℝPremetricSpace ]
closedAbsRadiusInclusionC radius =
  NE→C (closedAbsRadiusInclusionNE radius)


private
  symmetricEndpointsOrdered : ∀ radius →
    0ℝ ≤ℝ radius → (- radius) ≤ℝ radius
  symmetricEndpointsOrdered radius 0≤radius =
    ≤ℝ-trans (- radius) 0ℝ radius
      (subst ((- radius) ≤ℝ_) negZero
        (negPres≤ 0ℝ radius 0≤radius))
      0≤radius

  clampSymmetricLowerBound : ∀ radius →
    0ℝ ≤ℝ radius → ∀ x →
    (- radius) ≤ℝ clampInterval (- radius) radius x
  clampSymmetricLowerBound radius 0≤radius x =
    clampIntervalLowerBound (- radius) radius x

  clampSymmetricUpperBound : ∀ radius →
    0ℝ ≤ℝ radius → ∀ x →
    clampInterval (- radius) radius x ≤ℝ radius
  clampSymmetricUpperBound radius 0≤radius x =
    clampIntervalUpperBound (- radius) radius
      (symmetricEndpointsOrdered radius 0≤radius) x


clampSymmetricAbsBound : ∀ radius →
  0ℝ ≤ℝ radius → ∀ x →
  absℝ (clampInterval (- radius) radius x) ≤ℝ radius
clampSymmetricAbsBound radius 0≤radius x =
  subst (_≤ℝ radius)
    (sym (absAsMax clamped))
    (maxLeastUpperBound clamped (- clamped) radius
      (clampSymmetricUpperBound radius 0≤radius x)
      negativeClamped≤radius)
  where
  clamped : ℝ
  clamped = clampInterval (- radius) radius x

  negativeClamped≤radius : (- clamped) ≤ℝ radius
  negativeClamped≤radius =
    subst ((- clamped) ≤ℝ_) (negInvol radius)
      (negPres≤ (- radius) clamped
        (clampSymmetricLowerBound radius 0≤radius x))


closedAbsRadiusRetractionNE : ∀ radius →
  0ℝ ≤ℝ radius →
  NE[ ℝPremetricSpace , ClosedAbsRadiusPremetricSpace radius ]
fst (closedAbsRadiusRetractionNE radius 0≤radius) x =
  clampInterval (- radius) radius x
  , clampSymmetricAbsBound radius 0≤radius x
IsNonExpanding.pres≈
  (snd (closedAbsRadiusRetractionNE radius 0≤radius)) =
  clampIntervalPres∼ (- radius) radius


private
  absBound→symmetricBounds : ∀ radius x →
    absℝ x ≤ℝ radius →
    ((- radius) ≤ℝ x) × (x ≤ℝ radius)
  absBound→symmetricBounds radius x absx≤radius .fst =
    subst ((- radius) ≤ℝ_) (negInvol x)
      (negPres≤ (- x) radius
        (≤ℝ-trans (- x) (absℝ x) radius
          (negLeAbs x) absx≤radius))
  absBound→symmetricBounds radius x absx≤radius .snd =
    ≤ℝ-trans x (absℝ x) radius
      (leAbs x) absx≤radius


closedAbsRadiusRetractionSection : ∀ radius →
  (0≤radius : 0ℝ ≤ℝ radius) →
  ∀ point →
  fst (closedAbsRadiusRetractionNE radius 0≤radius)
      (fst (closedAbsRadiusInclusionNE radius) point)
    ≡ point
closedAbsRadiusRetractionSection radius 0≤radius point =
  Σ≡Prop
    (isPropClosedAbsRadiusMembership radius)
    (clampIntervalFix (- radius) radius (fst point)
      (fst bounds) (snd bounds))
  where
  bounds : ((- radius) ≤ℝ fst point) × (fst point ≤ℝ radius)
  bounds = absBound→symmetricBounds radius (fst point) (snd point)


closedAbsRadiusIsComplete : ∀ radius →
  0ℝ ≤ℝ radius →
  PremetricTheory.isComplete (ClosedAbsRadiusPremetricSpace radius)
closedAbsRadiusIsComplete radius 0≤radius =
  retractPresIsComplete
    isCompleteℝ
    (closedAbsRadiusInclusionNE radius)
    (closedAbsRadiusRetractionNE radius 0≤radius)
    (closedAbsRadiusRetractionSection radius 0≤radius)


closedAbsRadiusZero : ∀ radius →
  0ℝ ≤ℝ radius → ClosedAbsRadius radius
closedAbsRadiusZero radius 0≤radius =
  0ℝ
  , subst (_≤ℝ radius) (sym absZero) 0≤radius


closedAbsRadiusMonotoneNE : ∀ radius larger →
  radius ≤ℝ larger →
  NE[ ClosedAbsRadiusPremetricSpace radius
    , ClosedAbsRadiusPremetricSpace larger ]
fst (closedAbsRadiusMonotoneNE radius larger radius≤larger)
  (x , absx≤radius) =
  x , ≤ℝ-trans (absℝ x) radius larger absx≤radius radius≤larger
IsNonExpanding.pres≈
  (snd (closedAbsRadiusMonotoneNE radius larger radius≤larger))
  x y ε x∼y =
  x∼y

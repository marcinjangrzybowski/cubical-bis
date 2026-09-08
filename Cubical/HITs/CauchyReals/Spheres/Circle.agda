module Cubical.HITs.CauchyReals.Spheres.Circle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Nat using (zero)
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupIso)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Invariance
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity
import Cubical.HITs.CauchyReals.Circle.FundamentalGroup.Base as Previous
open import Cubical.HITs.CauchyReals.Foundation.Base

RealCircle∙ : PointedPremetricSpace ℓ-zero ℓ-zero
RealCircle∙ = CirclePremetricSpace , Previous.basepoint

-- The Cartesian unit circle is literally the one-dimensional real sphere.
-- We use the existing quotient-circle equivalence, including its metric.
private
  pullbackIsometry : (Y : PremetricSpace ℓ-zero ℓ-zero) {A : Type}
    (setA : isSet A) (f : A → fst Y) (equivF : isEquiv f)
    (injective : ∀ x y → f x ≡ f y → x ≡ y) →
    IsIsometry
      (snd (SubspaceAlongInjection.injectionPremetricSpace Y setA f injective))
      (f , equivF) (snd Y)
  pullbackIsometry Y setA f equivF injective = isisometry (λ p ε q → idEquiv _)

  opaque
    cartesianMetric : IsIsometry (snd CirclePremetricSpace)
      Circle≃distCircle (snd distCirclePremetricSpace)
    cartesianMetric = pullbackIsometry distCirclePremetricSpace isSetCircle
      Circle→distCircle isEquivCircle→distCircle
      (λ x y → invEq (congEquiv Circle≃distCircle))

    based : Circle→distCircle Previous.basepoint ≡ spherePoint 1
    based = injCircle0≡circle0 ∙
      distCircle≡ {x = circle0} {y = spherePoint 1} refl refl

opaque
  circle-sphere-isometry : PointedIsometry RealCircle∙ (RealSphere∙ 1)
  circle-sphere-isometry = (Circle≃distCircle , cartesianMetric) , based

circle-sphere-π₁ :
  GroupIso (realπGr zero RealCircle∙) (realπGr zero (RealSphere∙ 1))
circle-sphere-π₁ = subst
  (λ Z → GroupIso (realπGr zero RealCircle∙) (realπGr zero Z))
  (pointedIsometryPath {X = RealCircle∙} {Y = RealSphere∙ 1} circle-sphere-isometry)
  (idGroupIso {G = realπGr zero RealCircle∙})

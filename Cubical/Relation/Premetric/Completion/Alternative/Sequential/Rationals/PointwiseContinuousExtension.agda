module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.PointwiseContinuousExtension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Rationals.Base as ℚ hiding (isProp∼)

open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.PointwiseContinuousExtension
  as PointwiseContinuousExtensionDefinition

module E = PointwiseContinuousExtensionDefinition
  ℚPremetricSpace ℚPremetricSpace

module Real = E.S


-- The most compact exact condition says that the rational germ of `f` has
-- a merely existing limit at every real center.

IsEverywhereConvergentRational :
  (ℚ → Real.ℭ̂ₛ) → Type₀
IsEverywhereConvergentRational = E.IsEverywhereConvergent


EverywhereConvergentRationalRestriction : Type₀
EverywhereConvergentRationalRestriction =
  E.EverywhereConvergentRestriction


-- A rational-to-real map represents a pointwise-continuous real function
-- exactly when its completed graph is pointwise single-valued and merely
-- total.  `E.IsPointwiseContinuousRestriction` expands to:
--
--   * pointwise completion-centered continuity, and
--   * at every real input, mere existence of a jointly approximable output.

IsPointwiseContinuousRationalRestriction :
  (ℚ → Real.ℭ̂ₛ) → Type₀
IsPointwiseContinuousRationalRestriction =
  E.IsPointwiseContinuousRestriction


PointwiseContinuousRationalRestriction : Type₀
PointwiseContinuousRationalRestriction =
  Σ[ f ∈ (ℚ → Real.ℭ̂ₛ) ]
    IsPointwiseContinuousRationalRestriction f


PointwiseContinuousRealMap : Type₀
PointwiseContinuousRealMap = E.PointwiseContinuousMap


rationalRestrictionContinuousRealMapEquiv :
  PointwiseContinuousRationalRestriction ≃ PointwiseContinuousRealMap
rationalRestrictionContinuousRealMapEquiv =
  E.pointwiseContinuousRestrictionMapEquiv


everywhereConvergentRationalContinuousRealMapEquiv :
  EverywhereConvergentRationalRestriction ≃ PointwiseContinuousRealMap
everywhereConvergentRationalContinuousRealMapEquiv =
  E.everywhereConvergentRestrictionMapEquiv


liftPointwiseContinuousRationalRestriction :
  PointwiseContinuousRationalRestriction → PointwiseContinuousRealMap
liftPointwiseContinuousRationalRestriction =
  E.extendPointwiseContinuousRestriction


liftPointwiseContinuousRational :
  (f : ℚ → Real.ℭ̂ₛ) →
  IsPointwiseContinuousRationalRestriction f →
  Real.ℭ̂ₛ → Real.ℭ̂ₛ
liftPointwiseContinuousRational =
  E.liftPointwiseContinuousRestriction


liftEverywhereConvergentRational :
  (f : ℚ → Real.ℭ̂ₛ) →
  IsEverywhereConvergentRational f →
  Real.ℭ̂ₛ → Real.ℭ̂ₛ
liftEverywhereConvergentRational f convergent =
  E.liftPointwiseContinuousRestriction f
    (E.everywhereConvergent→pointwiseContinuousRestriction convergent)


restrictPointwiseContinuousRealMap :
  PointwiseContinuousRealMap → PointwiseContinuousRationalRestriction
restrictPointwiseContinuousRealMap =
  E.restrictPointwiseContinuousMap

module Cubical.HITs.CauchyReals.Circle.Winding where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.Data.Rationals using ([_/_])
open import Cubical.HITs.SetQuotients using (eq/)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity public using
  (CirclePremetricSpace; Circle→distCircleUC; injCircleUC; coverUC)
open import Cubical.HITs.CauchyReals.Circle.Winding.Loop public
open import Cubical.HITs.CauchyReals.Circle.Winding.Lift public using (windingLoop-lift; lift-step)
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle using (cover; cover-respects)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Uniform.Base using (IsUContinuous)
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures using (_∘UC_)

private
  interval-endpoints : injCircle 0 ≡ injCircle 1
  interval-endpoints = eq/ 0 1 (-1 , -ᵣ-rat₂ 0 1)

  cover-endpoints : cover 0 ≡ cover 1
  cover-endpoints = cover-respects 0 1 (-1 , -ᵣ-rat₂ 0 1)

-- Degree of a uniformly continuous map of the Cartesian unit circle.
distCircleWinding : UC[ distCirclePremetricSpace , distCirclePremetricSpace ] → ℤ
distCircleWinding f = windingLoop (f ∘UC coverUC)
  (cong (fst f) cover-endpoints)

distCircleWinding-spec :
  (f : UC[ distCirclePremetricSpace , distCirclePremetricSpace ]) →
  HasWinding (fst f ∘ cover) (distCircleWinding f)
distCircleWinding-spec f = windingLoop-spec (f ∘UC coverUC)
  (cong (fst f) cover-endpoints)

-- Degree of a uniformly continuous map of ℝ/ℤ, with its circle metric.
windingNumber : UC[ CirclePremetricSpace , CirclePremetricSpace ] → ℤ
windingNumber f = windingLoop (Circle→distCircleUC ∘UC (f ∘UC injCircleUC))
  (cong (Circle→distCircle ∘ fst f) interval-endpoints)

windingNumber-spec : (f : UC[ CirclePremetricSpace , CirclePremetricSpace ]) →
  HasWinding (Circle→distCircle ∘ fst f ∘ injCircle) (windingNumber f)
windingNumber-spec f = windingLoop-spec (Circle→distCircleUC ∘UC (f ∘UC injCircleUC))
  (cong (Circle→distCircle ∘ fst f) interval-endpoints)

windingNumber-lift : (f : UC[ CirclePremetricSpace , CirclePremetricSpace ]) →
  (g : ℝ → ℝ) → ∥ IsUContinuous g ∥₁ →
  (∀ x y → Circle→distCircle (fst f (injCircle x)) ℝS¹.+
    cover (g y -ᵣ g x) ≡ Circle→distCircle (fst f (injCircle y))) →
  rat [ windingNumber f / 1 ] ≡ g 1 -ᵣ g 0
windingNumber-lift f =
  windingLoop-lift (Circle→distCircleUC ∘UC (f ∘UC injCircleUC))
    (cong (Circle→distCircle ∘ fst f) interval-endpoints)

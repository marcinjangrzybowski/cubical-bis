module Cubical.HITs.CauchyReals.Circle.Winding.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.Data.Rationals as ℚ using (ℚ; [_/_])
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Uniform.Base
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Winding.Subdivision
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity
open import Cubical.HITs.CauchyReals.Circle.Winding.Loop
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

opaque
  shortAngle-identify : ∀ p q near t → absᵣ t <ᵣ rat [ 1 / 4 ] →
    p ℝS¹.+ cover t ≡ q → shortAngle p q near ≡ t
  shortAngle-identify p q near t bound step = cover-injective-near _ _
    (isTrans≤<ᵣ _ _ _ (absᵣ-triangle'' _ _)
      (isTrans<ᵣ _ (rat [ 1 / 4 ] +ᵣ rat [ 1 / 4 ]) _
        (<ᵣMonotone+ᵣ _ _ _ _ (shortAngle-bound p q near) bound)
        (isTrans≡<ᵣ _ _ _ (+ᵣ-rat _ _) decℚ<ᵣ?)))
    (ℝS¹.·CancelL p (shortAngle-step p q near ∙ sym step))

  lift-step : ∀ (f : ℝ → distCircle) base (g : ℝ → ℝ) →
    (∀ t → f t ≡ base ℝS¹.+ cover (g t)) → ∀ x y →
    f x ℝS¹.+ cover (g y -ᵣ g x) ≡ f y
  lift-step f base g lifts x y =
    cong (ℝS¹._+ cover (g y -ᵣ g x)) (lifts x)
    ∙ sym (ℝS¹.+Assoc _ _ _)
    ∙ cong (base ℝS¹.+_)
        (sym (cover-add _ _) ∙ cong cover ℝ!)
    ∙ sym (lifts y)

private
  module LiftSum (f : ℝ → distCircle) (g : ℝ → ℝ)
    (step : ∀ x y → f x ℝS¹.+ cover (g y -ᵣ g x) ≡ f y)
    (δ : ℚ₊)
    (close : ∀ x y → x ∼[ δ ] y → g x ∼[ [ 1 / 4 ]₊ ] g y)
    where

    module S = Subdivision (f ∘ rat)

    turns-lift : ∀ n a b a≤b fine → mesh n a b ℚ.< fst δ →
      S.turns n a b a≤b fine ≡ g (rat b) -ᵣ g (rat a)
    turns-lift zero a b a≤b fine bound = shortAngle-identify _ _ _ _
      (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _)
        (equivFun (∼≃abs<ε _ _ ([ 1 / 4 ]₊))
          (close (rat a) (rat b) (rat-rat-fromAbs a b δ
            (ℚ.isTrans≤< _ (b ℚ.- a) _
              (ℚ.absFrom≤×≤ (b ℚ.- a) (a ℚ.- b)
                <≤ℚ! <≤ℚ![ a≤b ])
              (subst (ℚ._< fst δ) (ℚ.·IdR _) bound))))))
      (step (rat a) (rat b))
    turns-lift (suc n) a b a≤b fine bound =
      cong₂ _+ᵣ_
        (turns-lift n a (mid a b) (mid-left a b a≤b) (fst fine)
          (subst (ℚ._< fst δ) (sym (mesh-left n a b)) bound))
        (turns-lift n (mid a b) b (mid-right a b a≤b) (snd fine)
          (subst (ℚ._< fst δ) (sym (mesh-right n a b)) bound))
      ∙ ℝ!

-- This identifies the constructed winding with the usual endpoint
-- displacement of any supplied uniformly continuous real lift.
windingLoop-lift : (f : UC[ ℝPremetricSpace , distCirclePremetricSpace ]) →
  (loop : fst f 0 ≡ fst f 1) → (g : ℝ → ℝ) → ∥ IsUContinuous g ∥₁ →
  (∀ x y → fst f x ℝS¹.+ cover (g y -ᵣ g x) ≡ fst f y) →
  rat [ windingLoop f loop / 1 ] ≡ g 1 -ᵣ g 0
windingLoop-lift f loop g gc step = PT.rec2 (isSetℝ _ _) calculate (snd f) gc
  where
  module S = Subdivision (fst f ∘ rat)

  calculate : (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
    (snd ℝPremetricSpace) (fst f) (snd distCirclePremetricSpace) μ) →
    IsUContinuous g → rat [ windingLoop f loop / 1 ] ≡ g 1 -ᵣ g 0
  calculate (μ , uc) gc = sym (windingLoop-subdivision f loop n fine)
    ∙ LiftSum.turns-lift (fst f) g step δg (snd (gc ([ 1 / 4 ]₊)))
        n 0 1 unit-order fine mesh<δg
    where
    δg = fst (gc ([ 1 / 4 ]₊))
    δ = min₊ (μ 1) δg
    n = fst (ℚ.1/2ⁿ<ε δ)

    mesh<δ : mesh n 0 1 ℚ.< fst δ
    mesh<δ = subst (ℚ._< fst δ) (sym (ℚ.·IdL _)) (snd (ℚ.1/2ⁿ<ε δ))

    mesh<δf : mesh n 0 1 ℚ.< fst (μ 1)
    mesh<δf = ℚ.isTrans<≤ _ _ _ mesh<δ (min₊≤L (μ 1) δg)

    mesh<δg : mesh n 0 1 ℚ.< fst δg
    mesh<δg = ℚ.isTrans<≤ _ _ _ mesh<δ (min₊≤R (μ 1) δg)

    fine : S.Fine n 0 1
    fine = S.fine-from-mesh n 0 1 unit-order (μ 1)
      (λ x y close → metric-close→Near (fst f (rat x)) (fst f (rat y))
        (IsUniformlyContinuousWith.pres≈ uc (rat x) (rat y) 1
          (∼→≈ℝ (rat x) (rat y) (μ 1) (rat-rat-fromAbs x y (μ 1) close))))
      mesh<δf

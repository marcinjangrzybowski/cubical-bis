module Cubical.HITs.CauchyReals.Circle.Homotopy.FiniteLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
import Cubical.Data.Rationals.Inverse as ℚ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Winding.Subdivision
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity
open import Cubical.HITs.CauchyReals.Circle.Winding.Loop
open import Cubical.HITs.CauchyReals.Circle.Homotopy.RealPaths
open import Cubical.HITs.CauchyReals.Circle.Homotopy.LocalLift
open import Cubical.HITs.CauchyReals.Circle.Homotopy.IntervalLift
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open IntervalLift

private
  opaque
    clamped-near-left : (a b : ℚ) → a ℚ.≤ b → (δ : ℚ₊) → b ℚ.- a ℚ.< fst δ →
      ∀ t → clampᵣ (rat a) (rat b) t ∼[ δ ] rat a
    clamped-near-left a b ab δ width t = invEq (∼≃abs<ε _ _ δ)
      (isTrans≤<ᵣ _ (rat b -ᵣ rat a) (rat (fst δ))
        (isTrans≡≤ᵣ _ _ _ (absᵣNonNeg _ nonnegative)
          (≤ᵣ-+o _ _ (-ᵣ rat a) (clamp≤ᵣ (rat a) (rat b) t)))
        (isTrans≡<ᵣ _ _ _ (-ᵣ-rat₂ b a) (<ℚ→<ᵣ _ _ width)))
      where
      nonnegative : 0 ≤ᵣ clampᵣ (rat a) (rat b) t -ᵣ rat a
      nonnegative = isTrans≡≤ᵣ _ _ _ (sym (+-ᵣ (rat a)))
        (≤ᵣ-+o _ _ (-ᵣ rat a) (≤clampᵣ (rat a) (rat b) t (≤ℚ→≤ᵣ a b ab)))

module FiniteLifting (f : CirclePath) (μ : ℚ₊ → ℚ₊)
  (fc : IsUniformlyContinuousWith (snd ℝPremetricSpace) (fst f) (snd distCirclePremetricSpace) μ)
  where

  private
    module S = Subdivision (fst f ∘ rat)
    module D = PremetricStr (snd distCirclePremetricSpace)

  radius : ℚ₊
  radius = min₊ (μ localLiftRadius) (μ 1)

  small-lift : ∀ a b → a ℚ.≤ b → b ℚ.- a ℚ.< fst radius →
    ∀ t → fst f (clampᵣ (rat a) (rat b) t) D.≈[ localLiftRadius ] fst f (rat a)
  small-lift a b ab width t = IsUniformlyContinuousWith.pres≈ fc _ _ localLiftRadius
    (∼→≈ℝ _ _ (μ localLiftRadius) (clamped-near-left a b ab (μ localLiftRadius)
      (ℚ.isTrans<≤ _ _ _ width (min₊≤L (μ localLiftRadius) (μ 1))) t))

  fine : ∀ n a b → (ab : a ℚ.≤ b) → mesh n a b ℚ.< fst radius → S.Fine n a b
  fine n a b ab width = S.fine-from-mesh n a b ab radius
    (λ x y xy → metric-close→Near (fst f (rat x)) (fst f (rat y))
      (IsUniformlyContinuousWith.pres≈ fc (rat x) (rat y) 1
        (∼→≈ℝ _ _ (μ 1) (rat-rat-fromAbs x y (μ 1)
          (ℚ.isTrans<≤ _ _ _ xy (min₊≤R (μ localLiftRadius) (μ 1))))))) width

  tree : ∀ n a b → a ℚ.≤ b → mesh n a b ℚ.< fst radius → IntervalLift f a b
  tree zero a b ab width = smallIntervalLift f a b ab
    (small-lift a b ab (subst (ℚ._< fst radius) (ℚ.·IdR _) width))
  tree (suc n) a b ab width = joinIntervalLift f a (mid a b) b
    (mid-left a b ab) (mid-right a b ab)
    (tree n a (mid a b) (mid-left a b ab)
      (subst (ℚ._< fst radius) (sym (mesh-left n a b)) width))
    (tree n (mid a b) b (mid-right a b ab)
      (subst (ℚ._< fst radius) (sym (mesh-right n a b)) width))

  tree-endpoint : ∀ n a b ab width →
    fst (path (tree n a b ab width)) (rat b) ≡ S.turns n a b ab (fine n a b ab width)
  tree-endpoint zero a b ab width = smallIntervalLift-endpoint f a b ab
    (small-lift a b ab (subst (ℚ._< fst radius) (ℚ.·IdR _) width)) _
  tree-endpoint (suc n) a b ab width = joinIntervalLift-endpoint f a (mid a b) b
    (mid-left a b ab) (mid-right a b ab) left right
    ∙ cong₂ _+ᵣ_
      (tree-endpoint n a (mid a b) (mid-left a b ab) left-width)
      (tree-endpoint n (mid a b) b (mid-right a b ab) right-width)
    where
    left-width : mesh n a (mid a b) ℚ.< fst radius
    left-width = subst (ℚ._< fst radius) (sym (mesh-left n a b)) width
    right-width : mesh n (mid a b) b ℚ.< fst radius
    right-width = subst (ℚ._< fst radius) (sym (mesh-right n a b)) width
    left : IntervalLift f a (mid a b)
    left = tree n a (mid a b) (mid-left a b ab) left-width
    right : IntervalLift f (mid a b) b
    right = tree n (mid a b) b (mid-right a b ab) right-width

  unit-lift : IntervalLift f 0 1
  unit-lift = tree n 0 1 unit-order width
    where
    n : ℕ
    n = fst (ℚ.1/2ⁿ<ε radius)
    width : mesh n 0 1 ℚ.< fst radius
    width = subst (ℚ._< fst radius) (sym (ℚ.·IdL _)) (snd (ℚ.1/2ⁿ<ε radius))

  unit-lift-endpoint : (loop : fst f 0 ≡ fst f 1) →
    fst (path unit-lift) 1 ≡ rat [ windingLoop f loop / 1 ]
  unit-lift-endpoint loop = tree-endpoint n 0 1 unit-order width
    ∙ windingLoop-subdivision f loop n (fine n 0 1 unit-order width)
    where
    n : ℕ
    n = fst (ℚ.1/2ⁿ<ε radius)
    width : mesh n 0 1 ℚ.< fst radius
    width = subst (ℚ._< fst radius) (sym (ℚ.·IdL _)) (snd (ℚ.1/2ⁿ<ε radius))

loopIntervalLift : (f : CirclePath) (loop : fst f 0 ≡ fst f 1) →
  ∥ Σ[ lifted ∈ IntervalLift f 0 1 ]
    fst (path lifted) 1 ≡ rat [ windingLoop f loop / 1 ] ∥₁
loopIntervalLift f loop = PT.map
  (λ (μ , fc) → FiniteLifting.unit-lift f μ fc , FiniteLifting.unit-lift-endpoint f μ fc loop)
  (snd f)

zeroLoopLift : (f : CirclePath) (loop : fst f 0 ≡ fst f 1) → windingLoop f loop ≡ 0 →
  ∥ Σ[ lifted ∈ IntervalLift f 0 1 ] fst (path lifted) 1 ≡ 0 ∥₁
zeroLoopLift f loop zero-winding = PT.map
  (λ (lifted , endpoint) → lifted , endpoint ∙ cong (λ k → rat [ k / 1 ]) zero-winding)
  (loopIntervalLift f loop)

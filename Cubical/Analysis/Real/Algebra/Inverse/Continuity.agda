module Cubical.Analysis.Real.Algebra.Inverse.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ; addIdL)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ; mulAssoc; mulIdL; mulIdR)
open import Cubical.Analysis.Real.Algebra.Inverse.Bounded
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (0≤→isNonnegative)
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Domain.OpenInterval
open import Cubical.Analysis.Real.Integration.UniformContinuity

opaque
  positiveReciprocalAtLowerBound : ∀ x (positive : 0ℝ <ℝ x) η → rat (fst η) ≤ℝ x →
    positiveReciprocal x positive ≡ boundedReciprocalℝ η x
  positiveReciprocalAtLowerBound x positive η lower =
    cong (positiveReciprocal x) (isProp<ℝ 0ℝ x positive ∣ gap ∣₁)
    ∙ positiveReciprocalAtGap x gap
    where
    gap : PositiveGap 0ℝ x
    gap = η , subst (_≤ℝ x) (sym (addIdL (rat (fst η)))) lower

  positiveReciprocalReverses≤ : ∀ x y (px : 0ℝ <ℝ x) (py : 0ℝ <ℝ y) → x ≤ℝ y →
    positiveReciprocal y py ≤ℝ positiveReciprocal x px
  positiveReciprocalReverses≤ x y px py lower = subst2 _≤ℝ_ cancel (mulIdR u)
    (mulPres≤L (x · v) 1ℝ u (0≤→isNonnegative u (<ℝ-weaken 0ℝ u (positiveReciprocalPositive x px)))
      (subst (x · v ≤ℝ_) (positiveReciprocalLaw y py)
        (mulPres≤R-0≤ x y v (<ℝ-weaken 0ℝ v (positiveReciprocalPositive y py)) lower)))
    where
    u v : ℝ
    u = positiveReciprocal x px
    v = positiveReciprocal y py
    cancel : u · (x · v) ≡ v
    cancel = mulAssoc u x v ∙ cong (_· v) (positiveReciprocalLaw' x px) ∙ mulIdL v

boundedReciprocalUniform : ∀ η → isUniformlyContinuous (ℝPremetricSpace .snd) (boundedReciprocalℝ η) (ℝPremetricSpace .snd)
boundedReciprocalUniform η = isLipschitz→isUniformlyContinuous _ _ _
  ∣ reciprocalLipschitzBound η , boundedReciprocalIsLipschitz η ∣₁

-- A common positive lower bound gives uniform continuity. This consumes
-- only the current radius of the input map, never a chosen family of radii.
positiveReciprocalUniformAlong : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
  (f : A → ℝ) (positive : ∀ x → 0ℝ <ℝ f x) η → (∀ x → rat (fst η) ≤ℝ f x) →
  IsRadiuswiseUniformlyContinuous source f (ℝPremetricSpace .snd) →
  IsRadiuswiseUniformlyContinuous source (λ x → positiveReciprocal (f x) (positive x)) (ℝPremetricSpace .snd)
positiveReciprocalUniformAlong source f positive η lower continuous ε = do
  (ρ , preserves) ← isUniformlyContinuous→isRadiuswiseUniformlyContinuous _ _ _ (boundedReciprocalUniform η) ε
  (δ , near) ← continuous ρ
  return (δ , λ x y close → subst2 (_∼[ ε ]_)
    (sym (positiveReciprocalAtLowerBound (f x) (positive x) η (lower x)))
    (sym (positiveReciprocalAtLowerBound (f y) (positive y) η (lower y)))
    (preserves (f x) (f y) (near x y close)))

-- The intrinsic positive-domain reciprocal is continuous without a uniform
-- lower bound on the whole domain. A single local gap suffices at each point.
positiveReciprocalIsContinuous : isContinuous (LowerOpenHalfLinePremetricSpace 0ℝ .snd)
  (λ x → positiveReciprocal (fst x) (snd x)) (ℝPremetricSpace .snd)
positiveReciprocalIsContinuous point .IsContinuousAt.pres≈ ε = do
  gap@(η , _) ← snd point
  let θ = η /2₊
      above : rat (fst θ) <ℝ fst point
      above = <≤ℝ-trans (rat (fst θ)) (rat (fst η)) (fst point)
        (<ℚ→<ℝ (fst θ) (fst η) (/2₊<id η)) (gapLowerBound {x = fst point} gap)
  (δ , staysAbove) ← lowerOpenHalfLineIsOpen (rat (fst θ)) (fst point) above
  (ρ , near) ← isUniformlyContinuous→isRadiuswiseUniformlyContinuous _ _ _ (boundedReciprocalUniform θ) ε
  return (min₊ δ ρ , λ other close → subst2 (_∼[ ε ]_)
    (sym (positiveReciprocalAtLowerBound (fst point) (snd point) θ (<ℝ-weaken (rat (fst θ)) (fst point) above)))
    (sym (positiveReciprocalAtLowerBound (fst other) (snd other) θ
      (<ℝ-weaken (rat (fst θ)) (fst other) (staysAbove (fst other) (monotone point other δ ρ close)))))
    (near (fst point) (fst other) (monotoneRight point other δ ρ close)))
  where
  monotone : ∀ (x y : LowerOpenHalfLine 0ℝ) δ ρ → fst x ∼[ min₊ δ ρ ] fst y → fst x ∼[ δ ] fst y
  monotone x y δ ρ = PremetricStr.isMonotone≈≤ (ℝPremetricSpace .snd) (fst x) (fst y) (min₊ δ ρ) δ (min₊≤L δ ρ)
  monotoneRight : ∀ (x y : LowerOpenHalfLine 0ℝ) δ ρ → fst x ∼[ min₊ δ ρ ] fst y → fst x ∼[ ρ ] fst y
  monotoneRight x y δ ρ = PremetricStr.isMonotone≈≤ (ℝPremetricSpace .snd) (fst x) (fst y) (min₊ δ ρ) ρ (min₊≤R δ ρ)

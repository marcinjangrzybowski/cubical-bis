module Cubical.HITs.CauchyReals.Circle.Winding.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Power.Order
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Uniform.Base
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.Metric.Compatibility.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base using
  (IsUContinuous·ᵣR)
open import Cubical.HITs.CauchyReals.Trigonometry.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Pi
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Winding.Subdivision
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace
open CategoryStructures using (_∘UC_)

private
  square-close : ∀ x y → x ≈ℝ[ 1 ] y →
    (x -ᵣ y) ·ᵣ (x -ᵣ y) <ᵣ 1
  square-close x y close = isTrans≡<ᵣ _ _ _
    (x·x≡∣x∣·∣x∣ (x -ᵣ y) ∙ sym (x^²=x·x (absᵣ (x -ᵣ y))))
    (^<1 _ (0≤absᵣ _) 1
      (equivFun (∼≃abs<ε x y 1) (≈ℝ→∼ x y 1 close)))

metric-close→Near : ∀ p q →
  PremetricStr._≈[_]_ (snd distCirclePremetricSpace) p 1 q → Near p q
metric-close→Near p q close = isTrans<≡ᵣ _ _ _
  (<ᵣMonotone+ᵣ _ 1 _ 1
    (square-close _ _ (fst close)) (square-close _ _ (snd close)))
  (+ᵣ-rat 1 1)

-- Only one positive continuity radius is needed to obtain a subdivision.
fine-uniform : (f : UC[ ℝPremetricSpace , distCirclePremetricSpace ]) →
  ∥ Σ[ n ∈ ℕ ] Subdivision.Fine (fst f ∘ rat) n 0 1 ∥₁
fine-uniform f = PT.map
  (λ (μ , μ-uc) → Subdivision.fine-exists (fst f ∘ rat) (μ 1)
    (λ x y close → metric-close→Near (fst f (rat x)) (fst f (rat y))
      (IsUniformlyContinuousWith.pres≈ μ-uc (rat x) (rat y) 1
        (∼→≈ℝ _ _ (μ 1) (rat-rat-fromAbs x y (μ 1) close)))))
  (snd f)

opaque
  unfolding cover
  cover-continuous : isUniformlyContinuous (snd ℝPremetricSpace) cover
    (snd distCirclePremetricSpace)
  cover-continuous = PT.map (λ uc → (λ ε → fst (uc ε)) , preserves uc)
    (IsUContinuous·ᵣR (2 ·ᵣ π-number))
    where
    preserves : (uc : IsUContinuous (_·ᵣ (2 ·ᵣ π-number))) →
      IsUniformlyContinuousWith (snd ℝPremetricSpace) cover
        (snd distCirclePremetricSpace) (λ ε → fst (uc ε))
    IsUniformlyContinuousWith.pres≈ (preserves uc) x y ε close =
      ∼→≈ℝ (fst (fst (cover x))) (fst (fst (cover y))) ε
        (subst∼ {0<ε = snd (one₊ ·₊ ε)} {0<ε' = snd ε} (ℚ.·IdL (fst ε))
          (Lipschitz-cos (x ·ᵣ (2 ·ᵣ π-number)) (y ·ᵣ (2 ·ᵣ π-number)) ε scaled)) ,
      ∼→≈ℝ (snd (fst (cover x))) (snd (fst (cover y))) ε
        (subst∼ {0<ε = snd (one₊ ·₊ ε)} {0<ε' = snd ε} (ℚ.·IdL (fst ε))
          (Lipschitz-sin (x ·ᵣ (2 ·ᵣ π-number)) (y ·ᵣ (2 ·ᵣ π-number)) ε scaled))
      where
      scaled : (x ·ᵣ (2 ·ᵣ π-number)) ∼[ ε ] (y ·ᵣ (2 ·ᵣ π-number))
      scaled = snd (uc ε) x y (≈ℝ→∼ x y (fst (uc ε)) close)

-- The standard positively oriented parametrization is uniformly continuous.
coverUC : UC[ ℝPremetricSpace , distCirclePremetricSpace ]
coverUC = cover , cover-continuous

private
  module CircleMetric = SubspaceAlongInjection distCirclePremetricSpace
    isSetCircle Circle→distCircle
    (λ x y → invEq (congEquiv Circle≃distCircle))

CirclePremetricSpace : PremetricSpace ℓ-zero ℓ-zero
CirclePremetricSpace = CircleMetric.injectionPremetricSpace

Circle→distCircleUC : UC[ CirclePremetricSpace , distCirclePremetricSpace ]
Circle→distCircleUC = NE→UC CircleMetric.injectionNE

injCircleUC : UC[ ℝPremetricSpace , CirclePremetricSpace ]
fst injCircleUC = injCircle
snd injCircleUC = PT.map (λ (μ , uc) → μ , preserves μ uc) (snd coverUC)
  where
  projection : ∀ x → cover x ≡ Circle→distCircle (injCircle x)
  projection x = cover-β x

  preserves : (μ : ℚ₊ → ℚ₊) →
    IsUniformlyContinuousWith (snd ℝPremetricSpace) cover (snd distCirclePremetricSpace) μ →
    IsUniformlyContinuousWith (snd ℝPremetricSpace) injCircle (snd CirclePremetricSpace) μ
  IsUniformlyContinuousWith.pres≈ (preserves μ uc) x y ε close =
    subst2 (λ p q → PremetricStr._≈[_]_ (snd distCirclePremetricSpace) p ε q)
      (projection x) (projection y)
      (IsUniformlyContinuousWith.pres≈ uc x y ε close)

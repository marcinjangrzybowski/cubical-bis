module Cubical.Analysis.Real.Integration.RiemannIntegral.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra


HasRiemannIntegralOn : (ℝ → ℝ) → ℝ → ℝ → ℝ → Type₀
HasRiemannIntegralOn f a b value =
  ∀ (ε : ℚ₊) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ (tagged : TaggedPartition[ a , b ]) →
        HasMeshBelow (TaggedPartition.partition tagged) δ →
        absℝ (riemannSum tagged f - value) <ℝ rat (fst ε))


isPropHasRiemannIntegralOn : ∀ f a b value →
  isProp (HasRiemannIntegralOn f a b value)
isPropHasRiemannIntegralOn f a b value hasValue hasValue' =
  funExt λ ε → squash₁ (hasValue ε) (hasValue' ε)


IsRiemannIntegrableOn : (ℝ → ℝ) → ℝ → ℝ → Type₀
IsRiemannIntegrableOn f a b =
  Σ[ value ∈ ℝ ] HasRiemannIntegralOn f a b value


integral : ∀ {f a b} → IsRiemannIntegrableOn f a b → ℝ
integral = fst


-- Every sequence of tagged partitions with vanishing mesh computes the same
-- integral, independently of how its partitions and tags were chosen.
riemannSumsConverge : ∀ {a b} (f : ℝ → ℝ) value
  (partitions : ℕ → TaggedPartition[ a , b ]) →
  HasVanishingMesh partitions →
  HasRiemannIntegralOn f a b value →
  isLimitSequence (λ n → riemannSum (partitions n) f) value
riemannSumsConverge f value partitions vanishing hasValue ε =
  PT.rec squash₁
    (λ { (δ , closeToValue) →
      PT.map
        (λ { (N , fineTail) →
          N , λ n N≤n →
            absDifference<→closeness
              (riemannSum (partitions n) f) value ε
              (closeToValue (partitions n) (fineTail n N≤n)) })
        (vanishing δ) })
    (hasValue ε)


fineTaggedPartition : ∀ a b → a ≤ℝ b →
  ∀ δ →
  ∃[ tagged ∈ TaggedPartition[ a , b ] ]
    HasMeshBelow (TaggedPartition.partition tagged) δ
fineTaggedPartition a b a≤b δ =
  PT.map
    (λ { (N , fineTail) →
      dyadicLeftTaggedPartition a b a≤b N
      , fineTail N ℕ.≤-refl })
    (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b δ)


riemannIntegralUnique : ∀ a b → a ≤ℝ b → ∀ f value value' →
  HasRiemannIntegralOn f a b value →
  HasRiemannIntegralOn f a b value' →
  value ≡ value'
riemannIntegralUnique a b a≤b f value value' hasValue hasValue' =
  cong fst
    (isPropSequenceLimit (λ n → riemannSum (partitions n) f)
      (value , riemannSumsConverge f value partitions vanishing hasValue)
      (value' , riemannSumsConverge f value' partitions vanishing hasValue'))
  where
  partitions = dyadicLeftTaggedPartition a b a≤b
  vanishing = dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b


isPropIsRiemannIntegrableOn : ∀ a b → a ≤ℝ b → ∀ f →
  isProp (IsRiemannIntegrableOn f a b)
isPropIsRiemannIntegrableOn a b a≤b f
  (value , hasValue) (value' , hasValue') =
  Σ≡Prop
    (λ candidate → isPropHasRiemannIntegralOn f a b candidate)
    (riemannIntegralUnique
      a b a≤b f value value' hasValue hasValue')

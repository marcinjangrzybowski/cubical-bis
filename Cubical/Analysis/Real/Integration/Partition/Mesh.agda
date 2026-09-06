module Cubical.Analysis.Real.Integration.Partition.Mesh where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.FinData using (Fin)
import Cubical.Data.FinData as FD
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; _≤₊_)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties using (negSub)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_; isProp<ℝ)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Sampling
open import Cubical.Analysis.Real.Integration.UniformContinuity


HasMeshBelow : ∀ {a b} → Partition[ a , b ] → ℚ₊ → Type₀
HasMeshBelow partition δ =
  ∀ i → width partition i <ℝ rat (fst δ)


isPropHasMeshBelow : ∀ {a b}
  (partition : Partition[ a , b ]) δ →
  isProp (HasMeshBelow partition δ)
isPropHasMeshBelow partition δ =
  isPropΠ λ i → isProp<ℝ (width partition i) (rat (fst δ))


meshBelowMonotone : ∀ {a b}
  (partition : Partition[ a , b ]) δ ε →
  δ ≤₊ ε →
  HasMeshBelow partition δ →
  HasMeshBelow partition ε
meshBelowMonotone partition δ ε δ≤ε mesh i =
  <≤ℝ-trans
    (width partition i) (rat (fst δ)) (rat (fst ε))
    (mesh i)
    (invEq (rat≤rat≃ (fst δ) (fst ε)) δ≤ε)


-- A partition scheme becomes fine one requested radius at a time.  Its tail
-- index remains truncated, matching the sequence witness hierarchy.
HasVanishingMesh : ∀ {a b} →
  (ℕ → TaggedPartition[ a , b ]) → Type₀
HasVanishingMesh partitions =
  ∀ δ →
    ∃[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n →
        HasMeshBelow (TaggedPartition.partition (partitions n)) δ)


isPropHasVanishingMesh : ∀ {a b}
  (partitions : ℕ → TaggedPartition[ a , b ]) →
  isProp (HasVanishingMesh partitions)
isPropHasVanishingMesh partitions =
  isPropΠ λ _ → squash₁


-- Any two points of one subinterval are separated by at most its width.
pointsInIntervalDistanceBound : ∀ lower upper x y →
  lower ≤ℝ x → x ≤ℝ upper →
  lower ≤ℝ y → y ≤ℝ upper →
  absℝ (x - y) ≤ℝ upper - lower
pointsInIntervalDistanceBound
  lower upper x y lower≤x x≤upper lower≤y y≤upper =
  absLeastUpperBound (x - y) (upper - lower)
    (≤ℝ-trans
      (x - y) (upper - y) (upper - lower)
      (addPres≤R x upper (- y) x≤upper)
      (addPres≤L (- y) (- lower) upper
        (negPres≤ lower y lower≤y)))
    (subst (_≤ℝ upper - lower) (sym (negSub x y))
      (≤ℝ-trans
        (y - x) (upper - x) (upper - lower)
        (addPres≤R y upper (- x) y≤upper)
        (addPres≤L (- x) (- lower) upper
          (negPres≤ lower x lower≤x))))


resampledTagsClose : ∀ {a b}
  (tagged : TaggedPartition[ a , b ]) δ
  (sample : Sampling (TaggedPartition.partition tagged)) →
  HasMeshBelow (TaggedPartition.partition tagged) δ →
  ∀ i →
  TaggedPartition.tags tagged i ∼[ δ ] Sampling.tags
    (TaggedPartition.partition tagged) sample i
resampledTagsClose tagged δ sample mesh i =
  absDifference<→closeness
    (TaggedPartition.tags tagged i)
    (Sampling.tags (TaggedPartition.partition tagged) sample i) δ
    (≤<ℝ-trans
      (absℝ
        (TaggedPartition.tags tagged i -
          Sampling.tags (TaggedPartition.partition tagged) sample i))
      (width (TaggedPartition.partition tagged) i)
      (rat (fst δ))
      (pointsInIntervalDistanceBound
        (Partition.points (TaggedPartition.partition tagged) (FD.weakenFin i))
        (Partition.points (TaggedPartition.partition tagged) (FD.suc i))
        (TaggedPartition.tags tagged i)
        (Sampling.tags (TaggedPartition.partition tagged) sample i)
        (TaggedPartition.lower≤tag tagged i)
        (TaggedPartition.tag≤upper tagged i)
        (Sampling.lower≤tag (TaggedPartition.partition tagged) sample i)
        (Sampling.tag≤upper (TaggedPartition.partition tagged) sample i))
      (mesh i))


RadiuswiseResamplingControl : (ℝ → ℝ) → ℚ₊ → Type₀
RadiuswiseResamplingControl f ε =
  ∃[ δ ∈ ℚ₊ ]
    (∀ {a b} (tagged : TaggedPartition[ a , b ])
      (sample : Sampling (TaggedPartition.partition tagged)) →
      HasMeshBelow (TaggedPartition.partition tagged) δ →
      ∀ i →
      f (TaggedPartition.tags tagged i) ∼[ ε ]
        f (Sampling.tags (TaggedPartition.partition tagged) sample i))


radiuswiseUniformContinuityControlsResampling : ∀ f →
  IsRadiuswiseUniformlyContinuousℝ f →
  ∀ ε → RadiuswiseResamplingControl f ε
radiuswiseUniformContinuityControlsResampling f f-uc ε =
  PT.map
    (λ { (δ , close) →
      δ , λ tagged sample mesh i →
        close _ _ (resampledTagsClose tagged δ sample mesh i) })
    (f-uc ε)

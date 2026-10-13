module Cubical.Analysis.Real.Integration.RiemannIntegral.CauchyCriterion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat as ℕ using (ℕ; max)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; ℚ₊≡)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic
open import Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic.Modulus
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base

RiemannCauchyRadius : (ℝ → ℝ) → ℝ → ℝ → ℚ₊ → ℚ₊ → Type₀
RiemannCauchyRadius f a b ε δ =
  ∀ (first second : TaggedPartition[ a , b ]) →
    HasMeshBelow (TaggedPartition.partition first) δ →
    HasMeshBelow (TaggedPartition.partition second) δ →
    riemannSum first f ∼[ ε ] riemannSum second f

IsRiemannCauchyOn : (ℝ → ℝ) → ℝ → ℝ → Type₀
IsRiemannCauchyOn f a b = ∀ ε → ∃[ δ ∈ ℚ₊ ] RiemannCauchyRadius f a b ε δ

isPropIsRiemannCauchyOn : ∀ f a b → isProp (IsRiemannCauchyOn f a b)
isPropIsRiemannCauchyOn f a b = isPropΠ λ _ → squash₁

opaque
  -- A radiuswise comparison identifies a supplied sequence limit with the
  -- semantic integral.  It does not manufacture a native Cauchy witness.
  riemannCauchyLimitIsIntegral : ∀ f a b
    (partitions : ℕ → TaggedPartition[ a , b ]) →
    HasVanishingMesh partitions → IsRiemannCauchyOn f a b →
    ∀ value → isLimitSequence (λ n → riemannSum (partitions n) f) value →
    HasRiemannIntegralOn f a b value
  riemannCauchyLimitIsIntegral f a b partitions mesh→0 stable value sums→value ε =
    PT.rec squash₁ (λ { (δ , compare) →
      PT.rec squash₁ (λ { (N , fine) →
        PT.map (λ { (M , close) → δ , λ tagged taggedFine →
          closeness→absDifference< (riemannSum tagged f) value ε
            (subst (λ ρ → riemannSum tagged f ∼[ ρ ] value)
              (ℚ₊≡ (1/2∈ℚ./2+/2≡id (fst ε)))
              (triangle∼ (riemannSum tagged f) (riemannSum (partitions (max N M)) f)
                value (ε /2₊) (ε /2₊)
                (compare tagged (partitions (max N M)) taggedFine
                  (fine (max N M) (ℕ.left-≤-max {m = N} {n = M})))
                (close (max N M) (ℕ.right-≤-max {n = M} {m = N})))) })
          (sums→value (ε /2₊)) }) (mesh→0 δ) }) (stable (ε /2₊))

  riemannCauchyModulusIsIntegrable : ∀ f a b → a ≤ℝ b →
    (μ : ℚ₊ → ℚ₊) → (∀ ε → RiemannCauchyRadius f a b ε (μ ε)) →
    IsRiemannIntegrableOn f a b
  riemannCauchyModulusIsIntegrable f a b a≤b μ compare =
    PT.rec (isPropIsRiemannIntegrableOn a b a≤b f)
      (λ { (n , length<n) →
        fromBound (naturalBound n) (<ℝ-weaken (b - a) (rat (naturalRational n)) length<n) })
      (∃naturalUpperBound (b - a))
    where
    partitions : ℕ → TaggedPartition[ a , b ]
    partitions = dyadicLeftTaggedPartition a b a≤b
    sums : ℕ → ℝ
    sums n = riemannSum (partitions n) f
    fromBound : (bound : ℚ₊) → b - a ≤ℝ rat (fst bound) → IsRiemannIntegrableOn f a b
    fromBound bound length≤bound = value
      , riemannCauchyLimitIsIntegral f a b partitions
        (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b)
        (λ ε → ∣ μ ε , compare ε ∣₁) value
        (limitOfSequenceIsLimit sums witness)
      where
      witness : SeqWitness sums
      witness = ∣ (λ ε → dyadicMeshModulus bound (μ ε))
        , (λ ε m n largeM largeN → compare ε (partitions m) (partitions n)
          (dyadicMeshModulusWorks a b a≤b bound (μ ε) length≤bound m largeM)
          (dyadicMeshModulusWorks a b a≤b bound (μ ε) length≤bound n largeN)) ∣₁
      value : ℝ
      value = limitOfSequence sums witness

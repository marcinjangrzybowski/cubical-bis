module Cubical.Analysis.Real.Integration.UniformContinuity.Bounded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.FinData using (FinVec)
import Cubical.Data.FinData as FD
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; 1₊)
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Lattice
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Slack
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Order
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.Partition.Cover
open import Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic

private
  finiteUpperBound : ∀ {n} → FinVec ℝ n → ℝ
  finiteUpperBound {zero} values = 0ℝ
  finiteUpperBound {suc n} values = maxℝ (values FD.zero) (finiteUpperBound (λ i → values (FD.suc i)))

  belowFiniteUpperBound : ∀ {n} (values : FinVec ℝ n) i → values i ≤ℝ finiteUpperBound values
  belowFiniteUpperBound {suc n} values FD.zero =
    left≤max (values FD.zero) (finiteUpperBound (λ i → values (FD.suc i)))
  belowFiniteUpperBound {suc n} values (FD.suc i) =
    ≤ℝ-trans (values (FD.suc i)) (finiteUpperBound (λ j → values (FD.suc j))) (finiteUpperBound values)
      (belowFiniteUpperBound (λ j → values (FD.suc j)) i)
      (right≤max (values FD.zero) (finiteUpperBound (λ j → values (FD.suc j))))

  sampleBound : ∀ {a b} → (ℝ → ℝ) → Partition[ a , b ] → ℝ
  sampleBound f partition = finiteUpperBound (λ i → absℝ (f (Partition.points partition i))) + rat (fst 1₊)

opaque
  private
    boundFromFinePartition : ∀ f a b δ →
      (∀ (x y : ClosedInterval a b) → fst x ∼[ δ ] fst y → f (fst x) ∼[ 1₊ ] f (fst y)) →
      (partition : Partition[ a , b ]) → HasMeshBelow partition δ →
      ∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (f x) ≤ℝ sampleBound f partition
    boundFromFinePartition f a b δ close partition mesh x lower upper =
      partitionCoversBound partition x (absℝ (f x)) (sampleBound f partition) lower upper
        (λ i path → subst (λ z → absℝ (f z) ≤ℝ sampleBound f partition) (sym path)
          (≤ℝ-trans (absℝ (f (points i))) maximum (sampleBound f partition)
            (belowFiniteUpperBound (λ j → absℝ (f (points j))) i)
            (subst (_≤ℝ sampleBound f partition) (addIdR maximum)
              (addPres≤L 0ℝ (rat (fst 1₊)) maximum (<ℝ-weaken 0ℝ (rat (fst 1₊)) (positiveSlack 1₊))))))
        cell
      where
      points : FinVec ℝ (suc (Partition.intervalCount partition))
      points = Partition.points partition
      maximum : ℝ
      maximum = finiteUpperBound (λ i → absℝ (f (points i)))
      cell : ∀ i → points (FD.weakenFin i) ≤ℝ x → x ≤ℝ points (FD.suc i) →
        absℝ (f x) ≤ℝ sampleBound f partition
      cell i cellLower cellUpper =
        subst (_≤ℝ sampleBound f partition) (cong absℝ (subAddCancel (f x) (f left)))
          (≤ℝ-trans (absℝ ((f x - f left) + f left)) (absℝ (f x - f left) + absℝ (f left))
            (sampleBound f partition) (absTriangle (f x - f left) (f left))
            (subst ((absℝ (f x - f left) + absℝ (f left)) ≤ℝ_)
              (addComm (rat (fst 1₊)) maximum)
              (addPres≤ (absℝ (f x - f left)) (rat (fst 1₊)) (absℝ (f left)) maximum
                (<ℝ-weaken (absℝ (f x - f left)) (rat (fst 1₊))
                  (closeness→absDifference< (f x) (f left) 1₊
                    (close (x , lower , upper)
                      (left , partitionPointLowerBound partition (FD.weakenFin i) , partitionPointUpperBound partition (FD.weakenFin i))
                      (absDifference<→closeness x left δ
                        (≤<ℝ-trans (absℝ (x - left)) (width partition i) (rat (fst δ))
                          (pointsInIntervalDistanceBound left (points (FD.suc i)) x left
                            cellLower cellUpper (≤ℝ-refl left) (Partition.monotone partition i)) (mesh i))))))
                (belowFiniteUpperBound (λ j → absℝ (f (points j))) (FD.weakenFin i)))))
        where
        left : ℝ
        left = points (FD.weakenFin i)

  -- Only continuity at tolerance one and one finite partition are used.
  -- The bound is truncated; no family of radii or sample bounds is chosen.
  radiuswiseUniformContinuityIsBoundedOn : ∀ f a b → a ≤ℝ b →
    IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
      (f ∘ fst) (ℝPremetricSpace .snd) →
    ∃[ bound ∈ ℚ₊ ] (∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (f x) ≤ℝ rat (fst bound))
  radiuswiseUniformContinuityIsBoundedOn f a b a≤b continuous =
    PT.rec squash₁ (λ { (δ , close) →
      PT.rec squash₁ (λ { (N , mesh) →
        PT.map (λ { (k , bound<k) → naturalBound k , λ x lower upper →
          ≤ℝ-trans (absℝ (f x)) (sampleBound f (dyadicEqualPartition a b a≤b N)) (rat (naturalRational k))
            (boundFromFinePartition f a b δ close (dyadicEqualPartition a b a≤b N) (mesh N ℕ.≤-refl) x lower upper)
            (<ℝ-weaken (sampleBound f (dyadicEqualPartition a b a≤b N)) (rat (naturalRational k)) bound<k) })
          (∃naturalUpperBound (sampleBound f (dyadicEqualPartition a b a≤b N))) })
        (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b δ) }) (continuous 1₊)

  uniformContinuityIsBoundedOn : ∀ f a b → a ≤ℝ b →
    isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (f ∘ fst) (ℝPremetricSpace .snd) →
    ∃[ bound ∈ ℚ₊ ] (∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (f x) ≤ℝ rat (fst bound))
  uniformContinuityIsBoundedOn f a b a≤b continuous =
    radiuswiseUniformContinuityIsBoundedOn f a b a≤b
      (isUniformlyContinuous→isRadiuswiseUniformlyContinuous
        (ClosedIntervalPremetricSpace a b .snd) (f ∘ fst) (ℝPremetricSpace .snd) continuous)

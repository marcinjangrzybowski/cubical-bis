module Cubical.Analysis.Real.Integration.Partition.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; FinVec)
import Cubical.Data.FinData as FD

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Integration.Partition


private
  finiteMonotoneLowerBound : ∀ {n}
    (points : FinVec ℝ (suc n)) →
    (∀ i → points (FD.weakenFin i) ≤ℝ points (FD.suc i)) →
    ∀ i → points FD.zero ≤ℝ points i
  finiteMonotoneLowerBound points monotone FD.zero =
    ≤ℝ-refl (points FD.zero)
  finiteMonotoneLowerBound {zero} points monotone (FD.suc ())
  finiteMonotoneLowerBound {suc n} points monotone (FD.suc i) =
    ≤ℝ-trans
      (points FD.zero) (points (FD.suc FD.zero)) (points (FD.suc i))
      (monotone FD.zero)
      (finiteMonotoneLowerBound (points ∘ FD.suc)
        (λ j → monotone (FD.suc j)) i)

  finiteMonotoneUpperBound : ∀ {n}
    (points : FinVec ℝ (suc n)) →
    (∀ i → points (FD.weakenFin i) ≤ℝ points (FD.suc i)) →
    ∀ i → points i ≤ℝ points (FD.fromℕ n)
  finiteMonotoneUpperBound {zero} points monotone FD.zero =
    ≤ℝ-refl (points FD.zero)
  finiteMonotoneUpperBound {zero} points monotone (FD.suc ())
  finiteMonotoneUpperBound {suc n} points monotone FD.zero =
    ≤ℝ-trans
      (points FD.zero) (points (FD.suc FD.zero))
      (points (FD.fromℕ (suc n)))
      (monotone FD.zero)
      (finiteMonotoneUpperBound (points ∘ FD.suc)
        (λ j → monotone (FD.suc j)) FD.zero)
  finiteMonotoneUpperBound {suc n} points monotone (FD.suc i) =
    finiteMonotoneUpperBound (points ∘ FD.suc)
      (λ j → monotone (FD.suc j)) i


opaque
  partitionPointLowerBound : ∀ {a b} (partition : Partition[ a , b ])
    (i : Fin (suc (Partition.intervalCount partition))) →
    a ≤ℝ Partition.points partition i
  partitionPointLowerBound partition i =
    subst (_≤ℝ Partition.points partition i)
      (Partition.leftEndpoint partition)
      (finiteMonotoneLowerBound
        (Partition.points partition) (Partition.monotone partition) i)

  partitionPointUpperBound : ∀ {a b} (partition : Partition[ a , b ])
    (i : Fin (suc (Partition.intervalCount partition))) →
    Partition.points partition i ≤ℝ b
  partitionPointUpperBound partition i =
    subst (Partition.points partition i ≤ℝ_)
      (Partition.rightEndpoint partition)
      (finiteMonotoneUpperBound
        (Partition.points partition) (Partition.monotone partition) i)

  partitionEndpointsOrdered : ∀ {a b} →
    Partition[ a , b ] → a ≤ℝ b
  partitionEndpointsOrdered {a} partition =
    subst (a ≤ℝ_) (Partition.rightEndpoint partition)
      (partitionPointLowerBound partition
        (FD.fromℕ (Partition.intervalCount partition)))

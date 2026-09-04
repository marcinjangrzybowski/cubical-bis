module Cubical.Analysis.Real.Integration.Partition where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin; FinVec)
import Cubical.Data.FinData as FD
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base


-- Dependent pairs are used instead of proof-bearing records here.  This keeps
-- endpoint and monotonicity proofs from becoming an eta-expansion interface
-- for the completed-real order.
Partition[_,_] : ℝ → ℝ → Type₀
Partition[ a , b ] =
  Σ[ intervalCount ∈ ℕ ]
  Σ[ points ∈ FinVec ℝ (suc intervalCount) ]
    (points FD.zero ≡ a)
  × (points (FD.fromℕ intervalCount) ≡ b)
  × ((i : Fin intervalCount) →
      points (FD.weakenFin i) ≤ℝ points (FD.suc i))


module Partition {a b : ℝ} (partition : Partition[ a , b ]) where
  intervalCount : ℕ
  intervalCount = fst partition

  points : FinVec ℝ (suc intervalCount)
  points = fst (snd partition)

  leftEndpoint : points FD.zero ≡ a
  leftEndpoint = fst (snd (snd partition))

  rightEndpoint : points (FD.fromℕ intervalCount) ≡ b
  rightEndpoint = fst (snd (snd (snd partition)))

  monotone : (i : Fin intervalCount) →
    points (FD.weakenFin i) ≤ℝ points (FD.suc i)
  monotone = snd (snd (snd (snd partition)))


TaggedPartition[_,_] : ℝ → ℝ → Type₀
TaggedPartition[ a , b ] =
  Σ[ partition ∈ Partition[ a , b ] ]
  Σ[ tags ∈ FinVec ℝ (Partition.intervalCount partition) ]
    ((i : Fin (Partition.intervalCount partition)) →
      Partition.points partition (FD.weakenFin i) ≤ℝ tags i)
  × ((i : Fin (Partition.intervalCount partition)) →
      tags i ≤ℝ Partition.points partition (FD.suc i))


module TaggedPartition {a b : ℝ}
    (tagged : TaggedPartition[ a , b ]) where
  partition : Partition[ a , b ]
  partition = fst tagged

  tags : FinVec ℝ (Partition.intervalCount partition)
  tags = fst (snd tagged)

  lower≤tag : (i : Fin (Partition.intervalCount partition)) →
    Partition.points partition (FD.weakenFin i) ≤ℝ tags i
  lower≤tag = fst (snd (snd tagged))

  tag≤upper : (i : Fin (Partition.intervalCount partition)) →
    tags i ≤ℝ Partition.points partition (FD.suc i)
  tag≤upper = snd (snd (snd tagged))

module Cubical.Analysis.Real.Integration.Partition.Sampling where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData using (Fin; FinVec)
import Cubical.Data.FinData as FD
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Integration.Partition


Sampling : ∀ {a b} → Partition[ a , b ] → Type₀
Sampling partition =
  Σ[ tags ∈ FinVec ℝ (Partition.intervalCount partition) ]
    ((i : Fin (Partition.intervalCount partition)) →
      Partition.points partition (FD.weakenFin i) ≤ℝ tags i)
  × ((i : Fin (Partition.intervalCount partition)) →
      tags i ≤ℝ Partition.points partition (FD.suc i))


module Sampling {a b : ℝ} (partition : Partition[ a , b ])
    (sample : Sampling partition) where
  tags : FinVec ℝ (Partition.intervalCount partition)
  tags = fst sample

  lower≤tag : (i : Fin (Partition.intervalCount partition)) →
    Partition.points partition (FD.weakenFin i) ≤ℝ tags i
  lower≤tag = fst (snd sample)

  tag≤upper : (i : Fin (Partition.intervalCount partition)) →
    tags i ≤ℝ Partition.points partition (FD.suc i)
  tag≤upper = snd (snd sample)


samplingToTaggedPartition : ∀ {a b}
  (partition : Partition[ a , b ]) →
  Sampling partition →
  TaggedPartition[ a , b ]
samplingToTaggedPartition partition sample =
  partition
  , Sampling.tags partition sample
  , Sampling.lower≤tag partition sample
  , Sampling.tag≤upper partition sample


leftSampling : ∀ {a b} (partition : Partition[ a , b ]) →
  Sampling partition
leftSampling partition =
  (λ i → Partition.points partition (FD.weakenFin i))
  , (λ i → ≤ℝ-refl
      (Partition.points partition (FD.weakenFin i)))
  , Partition.monotone partition


rightSampling : ∀ {a b} (partition : Partition[ a , b ]) →
  Sampling partition
rightSampling partition =
  (λ i → Partition.points partition (FD.suc i))
  , Partition.monotone partition
  , (λ i → ≤ℝ-refl
      (Partition.points partition (FD.suc i)))


leftTaggedPartition : ∀ {a b} →
  Partition[ a , b ] → TaggedPartition[ a , b ]
leftTaggedPartition partition =
  samplingToTaggedPartition partition (leftSampling partition)


rightTaggedPartition : ∀ {a b} →
  Partition[ a , b ] → TaggedPartition[ a , b ]
rightTaggedPartition partition =
  samplingToTaggedPartition partition (rightSampling partition)


taggedSampling : ∀ {a b} (tagged : TaggedPartition[ a , b ]) →
  Sampling (TaggedPartition.partition tagged)
taggedSampling tagged =
  TaggedPartition.tags tagged
  , TaggedPartition.lower≤tag tagged
  , TaggedPartition.tag≤upper tagged


resample : ∀ {a b}
  (tagged : TaggedPartition[ a , b ]) →
  Sampling (TaggedPartition.partition tagged) →
  TaggedPartition[ a , b ]
resample tagged sample =
  samplingToTaggedPartition (TaggedPartition.partition tagged) sample

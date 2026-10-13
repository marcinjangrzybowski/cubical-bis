module Cubical.Analysis.Real.Integration.Partition.Cover where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; FinVec)
import Cubical.Data.FinData as FD

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Overlap

-- A closed inequality can be proved cell by cell without deciding which
-- cell contains a real point. The separate node case includes partitions
-- with no cells and repeated endpoints.
private
  boundAlongPoints : ∀ n (points : FinVec ℝ (suc n)) x value bound →
    points FD.zero ≤ℝ x → x ≤ℝ points (FD.fromℕ n) →
    (∀ i → x ≡ points i → value ≤ℝ bound) →
    (∀ i → points (FD.weakenFin i) ≤ℝ x →
      x ≤ℝ points (FD.suc i) → value ≤ℝ bound) →
    value ≤ℝ bound
  boundAlongPoints zero points x value bound lower upper nodes cells =
    nodes FD.zero (≤ℝ-antisym x (points FD.zero) upper lower)
  boundAlongPoints (suc n) points x value bound lower upper nodes cells =
    orderCasesForBound x (points (FD.suc FD.zero)) value bound
      (cells FD.zero lower)
      (λ next≤x → boundAlongPoints n (λ i → points (FD.suc i)) x value bound
        next≤x upper (λ i → nodes (FD.suc i)) (λ i → cells (FD.suc i)))

opaque
  partitionCoversBound : ∀ {a b} (partition : Partition[ a , b ]) x value bound →
    a ≤ℝ x → x ≤ℝ b →
    (∀ i → x ≡ Partition.points partition i → value ≤ℝ bound) →
    (∀ i → Partition.points partition (FD.weakenFin i) ≤ℝ x →
      x ≤ℝ Partition.points partition (FD.suc i) → value ≤ℝ bound) →
    value ≤ℝ bound
  partitionCoversBound partition x value bound lower upper =
    boundAlongPoints (Partition.intervalCount partition) (Partition.points partition) x value bound
      (subst (_≤ℝ x) (sym (Partition.leftEndpoint partition)) lower)
      (subst (x ≤ℝ_) (sym (Partition.rightEndpoint partition)) upper)

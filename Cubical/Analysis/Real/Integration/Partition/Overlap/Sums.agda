module Cubical.Analysis.Real.Integration.Partition.Overlap.Sums where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.FinData using (Fin)
import Cubical.Data.FinData as FD
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.FiniteSum.Algebra
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Order
open import Cubical.Analysis.Real.Integration.Partition.Overlap
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra

private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)
open ℝSum using (∑)

opaque
  sumOverlapWidths : ∀ {a b} (p : Partition[ a , b ]) l r →
    a ≤ℝ l → l ≤ℝ r → r ≤ℝ b →
    ∑ (λ i → overlapWidth l r
      (Partition.points p (FD.weakenFin i))
      (Partition.points p (FD.suc i))) ≡ r - l
  sumOverlapWidths {a} {b} p l r a≤l l≤r r≤b =
    finiteSumTelescoping (clampInterval l r ∘ Partition.points p)
    ∙ cong₂ _-_
      (cong (clampInterval l r) (Partition.rightEndpoint p)
        ∙ clampAboveInterval l r b l≤r r≤b)
      (cong (clampInterval l r) (Partition.leftEndpoint p)
        ∙ clampBelowInterval l r a a≤l)

module _ {a b : ℝ} (p q : Partition[ a , b ]) where
  cellOverlap : Fin (Partition.intervalCount p) →
    Fin (Partition.intervalCount q) → ℝ
  cellOverlap i j = overlapWidth
    (Partition.points p (FD.weakenFin i)) (Partition.points p (FD.suc i))
    (Partition.points q (FD.weakenFin j)) (Partition.points q (FD.suc j))

  opaque
    cellOverlapRowSum : ∀ i → ∑ (cellOverlap i) ≡ width p i
    cellOverlapRowSum i = sumOverlapWidths q
      (Partition.points p (FD.weakenFin i)) (Partition.points p (FD.suc i))
      (partitionPointLowerBound p (FD.weakenFin i))
      (Partition.monotone p i) (partitionPointUpperBound p (FD.suc i))

    cellOverlapColumnSum : ∀ j → ∑ (λ i → cellOverlap i j) ≡ width q j
    cellOverlapColumnSum j =
      finiteSumExt (λ i → overlapWidthSymmetric
        (Partition.points p (FD.weakenFin i)) (Partition.points p (FD.suc i))
        (Partition.points q (FD.weakenFin j)) (Partition.points q (FD.suc j))
        (Partition.monotone p i) (Partition.monotone q j))
      ∙ sumOverlapWidths p
        (Partition.points q (FD.weakenFin j)) (Partition.points q (FD.suc j))
        (partitionPointLowerBound q (FD.weakenFin j))
        (Partition.monotone q j) (partitionPointUpperBound q (FD.suc j))

opaque
  riemannSumDifferenceOverOverlaps : ∀ {a b}
    (first second : TaggedPartition[ a , b ]) (f : ℝ → ℝ) →
    ∑ (λ i → ∑ (λ j →
      cellOverlap (TaggedPartition.partition first) (TaggedPartition.partition second) i j
      · (f (TaggedPartition.tags first i) - f (TaggedPartition.tags second j))))
    ≡ riemannSum first f - riemannSum second f
  riemannSumDifferenceOverOverlaps {a} {b} first second f =
    finiteSumExt (λ i →
      finiteSumExt (λ j → ℝRing.·DistR- (w i j) (x i) (y j))
      ∙ finiteSumSub (λ j → w i j · x i) (λ j → w i j · y j))
    ∙ finiteSumSub (λ i → ∑ (λ j → w i j · x i))
        (λ i → ∑ (λ j → w i j · y j))
    ∙ cong₂ _-_
      (finiteSumExt (λ i → sym (finiteSumMulRight (x i) (w i))
        ∙ cong (_· x i) (cellOverlapRowSum p q i)))
      (finiteSumExchange (λ i j → w i j · y j)
        ∙ finiteSumExt (λ j → sym (finiteSumMulRight (y j) (λ i → w i j))
          ∙ cong (_· y j) (cellOverlapColumnSum p q j)))
    where
    p : Partition[ a , b ]
    p = TaggedPartition.partition first
    q : Partition[ a , b ]
    q = TaggedPartition.partition second
    w : Fin (Partition.intervalCount p) → Fin (Partition.intervalCount q) → ℝ
    w = cellOverlap p q
    x : Fin (Partition.intervalCount p) → ℝ
    x i = f (TaggedPartition.tags first i)
    y : Fin (Partition.intervalCount q) → ℝ
    y j = f (TaggedPartition.tags second j)

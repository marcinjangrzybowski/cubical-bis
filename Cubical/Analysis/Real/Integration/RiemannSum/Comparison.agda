module Cubical.Analysis.Real.Integration.RiemannSum.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.FinData using (Fin)
import Cubical.Data.FinData as FD
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.FiniteSum.Algebra
open import Cubical.Analysis.Real.FiniteSum.Bounds
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Order
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.Partition.Overlap
open import Cubical.Analysis.Real.Integration.Partition.Overlap.Sums
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra

private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)
open ℝSum using (∑)

private opaque
  weightedOverlapDifferenceBound : ∀ a b c d x y u v (ε δ : ℚ₊) →
    a ≤ℝ b → c ≤ℝ d →
    a ≤ℝ x → x ≤ℝ b → c ≤ℝ y → y ≤ℝ d →
    b - a <ℝ rat (fst (δ /2₊)) → d - c <ℝ rat (fst (δ /2₊)) →
    (x ∼[ δ ] y → u ∼[ ε ] v) →
    absℝ (overlapWidth a b c d · (u - v)) ≤ℝ overlapWidth a b c d · rat (fst ε)
  weightedOverlapDifferenceBound a b c d x y u v ε δ a≤b c≤d
    a≤x x≤b c≤y y≤d firstSmall secondSmall close =
    orderCasesForBound b c (absℝ (w · (u - v))) (w · rat (fst ε))
      (λ b≤c → zeroCase (overlapWidthBefore a b c d a≤b b≤c c≤d))
      (λ c≤b → orderCasesForBound d a (absℝ (w · (u - v))) (w · rat (fst ε))
        (λ d≤a → zeroCase (overlapWidthAfter a b c d c≤d d≤a))
        (λ a≤d → subst (_≤ℝ w · rat (fst ε))
          (sym (absMul w (u - v)
            ∙ cong (_· absℝ (u - v)) (absOfNonnegative w w≥0)))
          (mulPres≤L (absℝ (u - v)) (rat (fst ε)) w
            (0≤→isNonnegative w w≥0)
            (<ℝ-weaken (absℝ (u - v)) (rat (fst ε))
              (closeness→absDifference< u v ε (close
                (absDifference<→closeness x y δ
                  (≤<ℝ-trans (absℝ (x - y)) ((b - a) + (d - c)) (rat (fst δ))
                    (overlappingTagsDistanceBound a b c d x y a≤x x≤b c≤y y≤d c≤b a≤d)
                    (subst (((b - a) + (d - c)) <ℝ_)
                      (rat+rat (fst (δ /2₊)) (fst (δ /2₊))
                        ∙ cong rat (1/2∈ℚ./2+/2≡id (fst δ)))
                      (<ℝ-add (b - a) (rat (fst (δ /2₊)))
                        (d - c) (rat (fst (δ /2₊))) firstSmall secondSmall))))))))))
    where
    w : ℝ
    w = overlapWidth a b c d
    w≥0 : 0ℝ ≤ℝ w
    w≥0 = overlapWidthNonnegative a b c d c≤d
    zeroCase : w ≡ 0ℝ → absℝ (w · (u - v)) ≤ℝ w · rat (fst ε)
    zeroCase w=0 = subst2 _≤ℝ_
      (sym (cong (λ z → absℝ (z · (u - v))) w=0
        ∙ cong absℝ (ℝRing.0LeftAnnihilates (u - v)) ∙ absZero))
      (sym (cong (_· rat (fst ε)) w=0 ∙ ℝRing.0LeftAnnihilates (rat (fst ε))))
      (≤ℝ-refl 0ℝ)

opaque
  riemannSumComparisonBound : ∀ {a b} (f : ℝ → ℝ) (ε δ : ℚ₊) →
    (∀ (x y : ClosedInterval a b) → fst x ∼[ δ ] fst y →
      f (fst x) ∼[ ε ] f (fst y)) →
    (first second : TaggedPartition[ a , b ]) →
    HasMeshBelow (TaggedPartition.partition first) (δ /2₊) →
    HasMeshBelow (TaggedPartition.partition second) (δ /2₊) →
    absℝ (riemannSum first f - riemannSum second f) ≤ℝ (b - a) · rat (fst ε)
  riemannSumComparisonBound {a} {b} f ε δ close first second firstMesh secondMesh =
    subst2 _≤ℝ_ (cong absℝ (riemannSumDifferenceOverOverlaps first second f))
      (finiteSumExt (λ i → sym (finiteSumMulRight e (w i))
        ∙ cong (_· e) (cellOverlapRowSum p q i))
        ∙ sym (finiteSumMulRight e (width p)) ∙ cong (_· e) (totalWidth p))
      (finiteSumAbsBoundBy (λ i → ∑ (λ j → w i j · (x i - y j)))
        (λ i → ∑ (λ j → w i j · e))
        (λ i → finiteSumAbsBoundBy (λ j → w i j · (x i - y j))
          (λ j → w i j · e) (cellBound i)))
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
    e : ℝ
    e = rat (fst ε)
    tagPoint : (tagged : TaggedPartition[ a , b ]) →
      Fin (Partition.intervalCount (TaggedPartition.partition tagged)) → ClosedInterval a b
    tagPoint tagged i = TaggedPartition.tags tagged i
      , ≤ℝ-trans a (Partition.points (TaggedPartition.partition tagged) (FD.weakenFin i))
          (TaggedPartition.tags tagged i)
          (partitionPointLowerBound (TaggedPartition.partition tagged) (FD.weakenFin i))
          (TaggedPartition.lower≤tag tagged i)
      , ≤ℝ-trans (TaggedPartition.tags tagged i)
          (Partition.points (TaggedPartition.partition tagged) (FD.suc i)) b
          (TaggedPartition.tag≤upper tagged i)
          (partitionPointUpperBound (TaggedPartition.partition tagged) (FD.suc i))
    cellBound : ∀ i j → absℝ (w i j · (x i - y j)) ≤ℝ w i j · e
    cellBound i j = weightedOverlapDifferenceBound
      (Partition.points p (FD.weakenFin i)) (Partition.points p (FD.suc i))
      (Partition.points q (FD.weakenFin j)) (Partition.points q (FD.suc j))
      (TaggedPartition.tags first i) (TaggedPartition.tags second j)
      (x i) (y j) ε δ (Partition.monotone p i) (Partition.monotone q j)
      (TaggedPartition.lower≤tag first i) (TaggedPartition.tag≤upper first i)
      (TaggedPartition.lower≤tag second j) (TaggedPartition.tag≤upper second j)
      (firstMesh i) (secondMesh j) (close (tagPoint first i) (tagPoint second j))

module Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; predℕ; _^_)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Int.Fast.Base as ℤ using (pos)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Order.Base using (_≤ℝ_)
open import Cubical.Analysis.Real.Order.AbsoluteValue using (leAbs)
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties using (≤<ℝ-trans)
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Geometric.Base
open import Cubical.Analysis.Real.Series.Geometric.Rational
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Sampling
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.Partition.Equal


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


dyadicIntervalCount : ℕ → ℕ
dyadicIntervalCount n = 2 ℕ.^ n


private
  powℚPath : ∀ q n → powℚ q n ≡ q ℚ.^ⁿ n
  powℚPath q zero = refl
  powℚPath q (suc n) =
    cong (q ℚ.·_) (powℚPath q n)

  dyadicIntervalCount-positive : ∀ n →
    0 ℕ.< dyadicIntervalCount n
  dyadicIntervalCount-positive n =
    ℕ.0<^ {m = 1} n

  dyadicParameter : ℕ → ℕ
  dyadicParameter n = predℕ (dyadicIntervalCount n)

  dyadicParameter-count : ∀ n →
    suc (dyadicParameter n) ≡ dyadicIntervalCount n
  dyadicParameter-count n =
    ℕ.k+predℕₖ {1} {dyadicIntervalCount n}
      (dyadicIntervalCount-positive n)

  canonicalPositiveNatural : ℕ → ℚ₊
  canonicalPositiveNatural k = fromNat (suc k)

  canonicalPositiveNatural-inverse : ∀ k →
    fst ((canonicalPositiveNatural k) ⁻¹₊) ≡
    [ pos 1 / 1+ k ]
  canonicalPositiveNatural-inverse = invℚ₊-fromNat

  dyadicStepFraction : ∀ n →
    [ pos 1 / 1+ dyadicParameter n ] ≡ halfℚ ^ⁿ n
  dyadicStepFraction n =
    sym (canonicalPositiveNatural-inverse (dyadicParameter n))
    ∙ cong (λ q → fst (q ⁻¹₊))
        (ℚ₊≡
          {x = canonicalPositiveNatural (dyadicParameter n)}
          {y = two₊ ℚ₊^ⁿ n}
          (cong (λ k → [ pos k / 1+ zero ])
              (dyadicParameter-count n)
          ∙ sym (ℚ.fromNat-^ 2 n)))
    ∙ invℚ₊-ℚ^ⁿ two₊ n

  halfℚ-nonnegative : 0 ℚ.≤ halfℚ
  halfℚ-nonnegative =
    ℚ.<Weaken≤ 0 halfℚ
      (subst (0 ℚ.<_) (sym halfℚPath) (ℚ.pos<pos tt))


dyadicEqualPartition : ∀ a b → a ≤ℝ b → ℕ → Partition[ a , b ]
dyadicEqualPartition a b a≤b n =
  equalPartition a b a≤b (dyadicParameter n)


dyadicLeftTaggedPartition : ∀ a b → a ≤ℝ b → ℕ →
  TaggedPartition[ a , b ]
dyadicLeftTaggedPartition a b a≤b n =
  leftTaggedPartition (dyadicEqualPartition a b a≤b n)


dyadicRightTaggedPartition : ∀ a b → a ≤ℝ b → ℕ →
  TaggedPartition[ a , b ]
dyadicRightTaggedPartition a b a≤b n =
  rightTaggedPartition (dyadicEqualPartition a b a≤b n)


dyadicReal : ℕ → ℝ
dyadicReal = geometricTerms (rat halfℚ)


dyadicEqualPartition-width : ∀ a b (a≤b : a ≤ℝ b) n
  (i : Fin (Partition.intervalCount
    (dyadicEqualPartition a b a≤b n))) →
  width (dyadicEqualPartition a b a≤b n) i ≡
  (b - a) · dyadicReal n
dyadicEqualPartition-width a b a≤b n i =
  equalPartition-width a b a≤b (dyadicParameter n) i
  ∙ cong ((b - a) ·_)
      (cong rat (dyadicStepFraction n)
      ∙ cong rat (sym (powℚPath halfℚ n))
      ∙ sym (pow-rat halfℚ n))


dyadicRealIsLimitZero : isLimitSequence dyadicReal 0ℝ
dyadicRealIsLimitZero =
  rationalGeometricPowersTendToZero
    halfℚ halfℚ-nonnegative (ℚ.isRefl≤ halfℚ)


dyadicWidthSequence : ℝ → ℝ → ℕ → ℝ
dyadicWidthSequence a b n = (b - a) · dyadicReal n


dyadicWidthIsLimitZero : ∀ a b →
  isLimitSequence (dyadicWidthSequence a b) 0ℝ
dyadicWidthIsLimitZero a b =
  subst (isLimitSequence (dyadicWidthSequence a b))
    (ℝRing.0RightAnnihilates (b - a))
    (mulPresIsLimitSequence
      (constantIsLimitSequence (b - a))
      dyadicRealIsLimitZero)


dyadicTaggedPartitions : ∀ a b (a≤b : a ≤ℝ b) →
  (∀ n → Sampling (dyadicEqualPartition a b a≤b n)) →
  ℕ → TaggedPartition[ a , b ]
dyadicTaggedPartitions a b a≤b samples n =
  samplingToTaggedPartition
    (dyadicEqualPartition a b a≤b n) (samples n)


dyadicTaggedPartitionsHaveVanishingMesh : ∀ a b (a≤b : a ≤ℝ b)
  (samples : ∀ n → Sampling (dyadicEqualPartition a b a≤b n)) →
  HasVanishingMesh (dyadicTaggedPartitions a b a≤b samples)
dyadicTaggedPartitionsHaveVanishingMesh a b a≤b samples δ =
  PT.map
    (λ { (N , close) →
      N , λ n N≤n i →
        subst (_<ℝ rat (fst δ))
          (sym (dyadicEqualPartition-width a b a≤b n i))
          (≤<ℝ-trans
            (dyadicWidthSequence a b n)
            (absℝ (dyadicWidthSequence a b n))
            (rat (fst δ))
            (leAbs (dyadicWidthSequence a b n))
            (subst (_<ℝ rat (fst δ))
              (cong absℝ (subZero (dyadicWidthSequence a b n)))
              (closeness→absDifference<
                (dyadicWidthSequence a b n) 0ℝ δ
                (close n N≤n)))) })
    (dyadicWidthIsLimitZero a b δ)


dyadicLeftTaggedPartitionsHaveVanishingMesh : ∀ a b
  (a≤b : a ≤ℝ b) →
  HasVanishingMesh (dyadicLeftTaggedPartition a b a≤b)
dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b =
  dyadicTaggedPartitionsHaveVanishingMesh a b a≤b
    (λ n → leftSampling (dyadicEqualPartition a b a≤b n))


dyadicRightTaggedPartitionsHaveVanishingMesh : ∀ a b
  (a≤b : a ≤ℝ b) →
  HasVanishingMesh (dyadicRightTaggedPartition a b a≤b)
dyadicRightTaggedPartitionsHaveVanishingMesh a b a≤b =
  dyadicTaggedPartitionsHaveVanishingMesh a b a≤b
    (λ n → rightSampling (dyadicEqualPartition a b a≤b n))

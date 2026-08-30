module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition.Equal where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc ; predℕ ; _^_)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.FinData using (Fin)
import Cubical.Data.FinData as FD
import Cubical.Data.FinData.Properties as FDP
open import Cubical.Data.Int.Fast.Base as ℤ using (pos ; _-_)
import Cubical.Data.Int.Fast.Properties as ℤ
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Tactics.CommRingSolver.Reflection

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation
  using (≤→zero≤difference)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (mul-preserves≤-left-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_ ; ≤<ℝ-trans)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (closeness→absDifference<)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Equality
  using (dyadicRadius ; dyadicReal ; dyadicRealIsCauchySequence ; dyadicReal-limit-zero)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition.Mesh


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


-- `equalPartition n` has `suc n` intervals.  Vertex `k` is the affine point
-- a + (b-a) k/(n+1).  All vertices are defined directly in the completed
-- reals; constructing a sequence of these partitions therefore involves no
-- rational approximation choices.

equalFraction : (n : ℕ) → Fin (suc (suc n)) → ℚ
equalFraction n k = [ pos (FD.toℕ k) / 1+ n ]


private
  equalFraction-lower : ∀ n (i : Fin (suc n)) →
    equalFraction n (FD.weakenFin i) ≡
    [ pos (FD.toℕ i) / 1+ n ]
  equalFraction-lower n i =
    cong (λ k → [ pos k / 1+ n ]) (FDP.weakenRespToℕ i)

  equalFraction-step≤ : ∀ n (i : Fin (suc n)) →
    equalFraction n (FD.weakenFin i) ℚ.≤
    equalFraction n (FD.suc i)
  equalFraction-step≤ n i =
    subst (ℚ._≤ equalFraction n (FD.suc i))
      (sym (equalFraction-lower n i))
      ([k/n]≤[k'/n]
        (pos (FD.toℕ i)) (pos (suc (FD.toℕ i))) (1+ n)
        (ℤ.ℕ≤→pos-≤-pos
          (FD.toℕ i) (suc (FD.toℕ i)) ℕ.≤-sucℕ))

  sameDenomSubSucc : ∀ m d →
    (([_/_] (pos (suc m)) d) ℚ.- ([_/_] (pos m) d)) ≡
    ([_/_] (pos (suc m) - pos m) d)
  sameDenomSubSucc m d = eq/ _ _ ℤ!

  equalFraction-step : ∀ n (i : Fin (suc n)) →
    equalFraction n (FD.suc i) ℚ.-
    equalFraction n (FD.weakenFin i) ≡
    [ pos 1 / 1+ n ]
  equalFraction-step n i =
    cong (λ q → equalFraction n (FD.suc i) ℚ.- q)
      (equalFraction-lower n i)
    ∙ sameDenomSubSucc (FD.toℕ i) (1+ n)
    ∙ cong (λ z → [ z / 1+ n ]) ℤ!


equalPartition : ∀ a b → a ≤ℝ b → ℕ → Partition[ a , b ]
equalPartition a b a≤b n .Partition[_,_].intervalCount = suc n
equalPartition a b a≤b n .Partition[_,_].points k =
  a Add.+ ((b Group.- a) Mul.· Real.ιℚ (equalFraction n k))
equalPartition a b a≤b n .Partition[_,_].leftEndpoint =
  cong (a Add.+_)
    (cong ((b Group.- a) Mul.·_)
      (cong Real.ιℚ (ℚ.[0/n]≡[0/m] n zero))
    ∙ mul-zero-right (b Group.- a))
  ∙ add-zero-right a
equalPartition a b a≤b n .Partition[_,_].rightEndpoint =
  cong (a Add.+_)
    (cong ((b Group.- a) Mul.·_)
      (cong Real.ιℚ
        (cong (λ k → [ pos k / 1+ n ]) (FD.toFromId (suc n))
        ∙ ℚ.[n/n]≡[m/m] n zero))
    ∙ mul-one-right (b Group.- a))
  ∙ add-comm a (b Group.- a)
  ∙ sub-add-cancel b a
equalPartition a b a≤b n .Partition[_,_].monotone i =
  add-preserves≤-left
    ((b Group.- a) Mul.·
      Real.ιℚ (equalFraction n (FD.weakenFin i)))
    ((b Group.- a) Mul.·
      Real.ιℚ (equalFraction n (FD.suc i)))
    a
    (mul-preserves≤-left-nonnegative
      (Real.ιℚ (equalFraction n (FD.weakenFin i)))
      (Real.ιℚ (equalFraction n (FD.suc i)))
      (b Group.- a)
      (≤ℚ→≤ℝ
        (equalFraction n (FD.weakenFin i))
        (equalFraction n (FD.suc i))
        (equalFraction-step≤ n i))
      (≤→zero≤difference a b a≤b))


equalPartition-width : ∀ a b (a≤b : a ≤ℝ b) n
  (i : Fin (suc n)) →
  width (equalPartition a b a≤b n) i ≡
  (b Group.- a) Mul.· Real.ιℚ [ pos 1 / 1+ n ]
equalPartition-width a b a≤b n i =
  sym (ℝRing.translatedDifference a
    ((b Group.- a) Mul.· Real.ιℚ (equalFraction n (FD.suc i)))
    ((b Group.- a) Mul.·
      Real.ιℚ (equalFraction n (FD.weakenFin i))))
  ∙ sym (ℝRing.·DistR-
    (b Group.- a)
    (Real.ιℚ (equalFraction n (FD.suc i)))
    (Real.ιℚ (equalFraction n (FD.weakenFin i))))
  ∙ cong ((b Group.- a) Mul.·_)
      (sub-ι-ι
        (equalFraction n (FD.suc i))
        (equalFraction n (FD.weakenFin i)))
  ∙ cong (λ q → (b Group.- a) Mul.· Real.ιℚ q)
      (equalFraction-step n i)


equalLeftTaggedPartition : ∀ a b → a ≤ℝ b → ℕ →
  TaggedPartition[ a , b ]
equalLeftTaggedPartition a b a≤b n =
  leftTaggedPartition (equalPartition a b a≤b n)


equalRightTaggedPartition : ∀ a b → a ≤ℝ b → ℕ →
  TaggedPartition[ a , b ]
equalRightTaggedPartition a b a≤b n =
  rightTaggedPartition (equalPartition a b a≤b n)


equalMidpointTaggedPartition : ∀ a b → a ≤ℝ b → ℕ →
  TaggedPartition[ a , b ]
equalMidpointTaggedPartition a b a≤b n =
  midpointTaggedPartition (equalPartition a b a≤b n)


-- Dyadic specialization -------------------------------------------------

dyadicIntervalCount : ℕ → ℕ
dyadicIntervalCount n = 2 ℕ.^ n


private
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

  two₊ : ℚ₊
  two₊ =
    [ pos 2 / 1+ zero ] , ℚAbs.0<pos 1 (1+ zero)

  twoInverseHalf :
    fst (two₊ ⁻¹₊) ≡ fst [ 1 / 2 ]₊
  twoInverseHalf =
    cong (λ q → fst (q ⁻¹₊))
      (ℚ₊≡ {x = two₊} {y = fromNat 2} refl)
    ∙ invℚ₊-fromNat 1

  canonicalPositiveNatural : ℕ → ℚ₊
  canonicalPositiveNatural k = fromNat (suc k)

  canonicalPositiveNatural-inverse : ∀ k →
    fst ((canonicalPositiveNatural k) ⁻¹₊) ≡
    [ pos 1 / 1+ k ]
  canonicalPositiveNatural-inverse = invℚ₊-fromNat

  dyadicStepFraction : ∀ n →
    [ pos 1 / 1+ dyadicParameter n ] ≡
    fst (dyadicRadius n)
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
    ∙ cong (λ q → q ^ⁿ n) twoInverseHalf


dyadicEqualPartition : ∀ a b → a ≤ℝ b → ℕ →
  Partition[ a , b ]
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


dyadicMidpointTaggedPartition : ∀ a b → a ≤ℝ b → ℕ →
  TaggedPartition[ a , b ]
dyadicMidpointTaggedPartition a b a≤b n =
  midpointTaggedPartition (dyadicEqualPartition a b a≤b n)


dyadicEqualPartition-width : ∀ a b (a≤b : a ≤ℝ b) n
  (i : Fin (Partition[_,_].intervalCount
    (dyadicEqualPartition a b a≤b n))) →
  width (dyadicEqualPartition a b a≤b n) i ≡
  (b Group.- a) Mul.· dyadicReal n
dyadicEqualPartition-width a b a≤b n i =
  equalPartition-width a b a≤b (dyadicParameter n) i
  ∙ cong (λ q → (b Group.- a) Mul.· Real.ιℚ q)
      (dyadicStepFraction n)


dyadicRealIsLimitZero :
    isLimitSequence dyadicReal (Real.ιℚ 0)
dyadicRealIsLimitZero =
    subst (isLimitSequence dyadicReal)
      dyadicReal-limit-zero
      (limitOfCauchySequenceIsLimit
        dyadicReal dyadicRealIsCauchySequence)

dyadicWidthSequence : Real.ℝ → Real.ℝ → ℕ → Real.ℝ
dyadicWidthSequence a b n =
  (b Group.- a) Mul.· dyadicReal n

dyadicWidthIsLimitZero : ∀ a b →
  isLimitSequence (dyadicWidthSequence a b) (Real.ιℚ 0)
dyadicWidthIsLimitZero a b =
  subst (isLimitSequence (dyadicWidthSequence a b))
    (mul-zero-right (b Group.- a))
    (mulPresIsLimitSequence
      (constantIsLimitSequence (b Group.- a))
      dyadicRealIsLimitZero)


-- Sampling is kept as a parameter.  Left endpoints, right endpoints, and a
-- future midpoint sampler therefore share the same geometric construction
-- and the same vanishing-mesh proof.

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
        subst
          (λ z → z <ℝ Real.ιℚ (fst δ))
          (sym (dyadicEqualPartition-width a b a≤b n i))
          (≤<ℝ-trans
            (dyadicWidthSequence a b n)
            (Abs.absℝ (dyadicWidthSequence a b n))
            (Real.ιℚ (fst δ))
            (x≤abs (dyadicWidthSequence a b n))
            (subst
              (λ z → z <ℝ Real.ιℚ (fst δ))
              (cong Abs.absℝ
                (sub-zero-right (dyadicWidthSequence a b n)))
              (closeness→absDifference<
                (dyadicWidthSequence a b n)
                (Real.ιℚ 0) δ
                (close n N≤n)))) })
    (dyadicWidthIsLimitZero a b δ)


dyadicLeftTaggedPartitionsHaveVanishingMesh : ∀ a b (a≤b : a ≤ℝ b) →
  HasVanishingMesh (dyadicLeftTaggedPartition a b a≤b)
dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b =
  dyadicTaggedPartitionsHaveVanishingMesh a b a≤b
    (λ n → leftSampling (dyadicEqualPartition a b a≤b n))


dyadicRightTaggedPartitionsHaveVanishingMesh : ∀ a b (a≤b : a ≤ℝ b) →
  HasVanishingMesh (dyadicRightTaggedPartition a b a≤b)
dyadicRightTaggedPartitionsHaveVanishingMesh a b a≤b =
  dyadicTaggedPartitionsHaveVanishingMesh a b a≤b
    (λ n → rightSampling (dyadicEqualPartition a b a≤b n))


dyadicMidpointTaggedPartitionsHaveVanishingMesh :
  ∀ a b (a≤b : a ≤ℝ b) →
  HasVanishingMesh (dyadicMidpointTaggedPartition a b a≤b)
dyadicMidpointTaggedPartitionsHaveVanishingMesh a b a≤b =
  dyadicTaggedPartitionsHaveVanishingMesh a b a≤b
    (λ n → midpointSampling (dyadicEqualPartition a b a≤b n))

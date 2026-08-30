module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (zero ; suc)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  oneℝ : Real.ℝ
  oneℝ = CommRingStr.1r (snd ℝCommRing)


geometricTerms : Real.ℝ → RealSequence
geometricTerms x n = x ^ⁿ n


-- This finite identity is entirely algebraic.  In particular it does not
-- consume any Cauchy modulus or open any truncation.

geometricPartialSum : ∀ x n →
  (oneℝ Group.- x) Mul.· partialSum (geometricTerms x) n ≡
  oneℝ Group.- x ^ⁿ n
geometricPartialSum x zero =
  mul-zero-right (oneℝ Group.- x)
  ∙ sym (sub-self oneℝ)
geometricPartialSum x (suc n) =
    mul-distrib-over-add-right
      (oneℝ Group.- x)
      (partialSum (geometricTerms x) n)
      (x ^ⁿ n)
  ∙ cong (Add._+ ((oneℝ Group.- x) Mul.· (x ^ⁿ n)))
      (geometricPartialSum x n)
  ∙ geometricTail
  where
  p : Real.ℝ
  p = x ^ⁿ n

  q : Real.ℝ
  q = x Mul.· p

  geometricTail :
    (oneℝ Group.- p) Add.+ (oneℝ Group.- x) Mul.· p ≡
    oneℝ Group.- q
  geometricTail =
    cong ((oneℝ Group.- p) Add.+_)
      (ℝRing.·DistL- oneℝ x p)
    ∙ cong ((oneℝ Group.- p) Add.+_)
        (cong (Group._- q) (mul-one-left p))
    ∙ add-assoc (oneℝ Group.- p) p (Neg.- q)
    ∙ cong (Group._- q)
        (sub-add-cancel oneℝ p)


geometricPartialSumByReciprocal :
  ∀ x n (positive-denominator : zeroℝ <ℝ oneℝ Group.- x) →
  partialSum (geometricTerms x) n ≡
  positiveReciprocal
    (oneℝ Group.- x) positive-denominator Mul.·
    (oneℝ Group.- x ^ⁿ n)
geometricPartialSumByReciprocal
    x n positive-denominator =
    sym (mul-one-left partial)
  ∙ cong (Mul._· partial)
      (sym
        (positiveReciprocalLaw'
          (oneℝ Group.- x) positive-denominator))
  ∙ sym (mul-assoc reciprocal (oneℝ Group.- x) partial)
  ∙ cong (reciprocal Mul.·_)
      (geometricPartialSum x n)
  where
  partial : Real.ℝ
  partial = partialSum (geometricTerms x) n

  reciprocal : Real.ℝ
  reciprocal =
    positiveReciprocal
      (oneℝ Group.- x) positive-denominator

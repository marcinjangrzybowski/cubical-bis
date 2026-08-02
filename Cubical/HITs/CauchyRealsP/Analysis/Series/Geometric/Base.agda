module Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

geometricTerms : ℝ → RealSequence
geometricTerms x n =
  x ^ⁿ n

geometricPartialSum : ∀ x n →
  (1 - x) · partialSum (geometricTerms x) n ≡
  1 - x ^ⁿ n
geometricPartialSum x zero =
  mulZeroR (1 - x)
  ∙ sym (subSelf 1)
geometricPartialSum x (suc n) =
  mulDistR
    (1 - x)
    (partialSum (geometricTerms x) n)
    (x ^ⁿ n)
  ∙ cong (_+ ((1 - x) · (x ^ⁿ n)))
      (geometricPartialSum x n)
  ∙ geometricTail
  where
  p : ℝ
  p =
    x ^ⁿ n

  q : ℝ
  q =
    x · p

  geometricTail :
    (1 - p) + (1 - x) · p ≡
    1 - q
  geometricTail =
    cong ((1 - p) +_)
      (ℝRing.·DistL- 1 x p)
    ∙ cong ((1 - p) +_)
        (cong (_- q) (mulIdL p))
    ∙ addAssoc (1 - p) p (- q)
    ∙ cong (_- q)
        (subAddCancel 1 p)

geometricPartialSumByReciprocal :
  ∀ x n (positive-denominator : 0 <ℝ 1 - x) →
  partialSum (geometricTerms x) n ≡
  positiveReciprocal
    (1 - x) positive-denominator
    · (1 - x ^ⁿ n)
geometricPartialSumByReciprocal
  x n positive-denominator =
    sym (mulIdL partial)
    ∙ cong (_· partial)
        (sym
          (positiveReciprocalLaw'
            (1 - x) positive-denominator))
    ∙ mulAssoc reciprocal (1 - x) partial
    ∙ cong (reciprocal ·_)
        (geometricPartialSum x n)
  where
  partial : ℝ
  partial =
    partialSum (geometricTerms x) n

  reciprocal : ℝ
  reciprocal =
    positiveReciprocal
      (1 - x) positive-denominator

module Cubical.Analysis.Real.Series.Geometric.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ; zero; suc)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
  using (subAddCancel)
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Series.Base


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


geometricTerms : ℝ → RealSequence
geometricTerms x n = powℝ x n


-- The identity is stated without division, so it remains valid at ratio one.

geometricPartialSum : ∀ x n →
  (1ℝ - x) · partialSum (geometricTerms x) n ≡
  1ℝ - powℝ x n
geometricPartialSum x zero =
  ℝRing.0RightAnnihilates (1ℝ - x)
  ∙ sym (subSelf 1ℝ)
geometricPartialSum x (suc n) =
  mulDistR
    (1ℝ - x)
    (partialSum (geometricTerms x) n)
    (powℝ x n)
  ∙ cong (_+ ((1ℝ - x) · powℝ x n))
      (geometricPartialSum x n)
  ∙ geometricTail
  where
  p : ℝ
  p = powℝ x n

  q : ℝ
  q = x · p

  geometricTail :
    (1ℝ - p) + (1ℝ - x) · p ≡
    1ℝ - q
  geometricTail =
    cong ((1ℝ - p) +_)
      (ℝRing.·DistL- 1ℝ x p)
    ∙ cong ((1ℝ - p) +_)
        (cong (_- q) (mulIdL p))
    ∙ addAssoc (1ℝ - p) p (- q)
    ∙ cong (_- q) (subAddCancel 1ℝ p)


geometricPartialSumByReciprocal :
  ∀ x n (positive-denominator : 0ℝ <ℝ 1ℝ - x) →
  partialSum (geometricTerms x) n ≡
  positiveReciprocal (1ℝ - x) positive-denominator
    · (1ℝ - powℝ x n)
geometricPartialSumByReciprocal
    x n positive-denominator =
  sym (mulIdL partial)
  ∙ cong (_· partial)
      (sym
        (positiveReciprocalLaw'
          (1ℝ - x) positive-denominator))
  ∙ sym (mulAssoc reciprocal (1ℝ - x) partial)
  ∙ cong (reciprocal ·_)
      (geometricPartialSum x n)
  where
  partial : ℝ
  partial = partialSum (geometricTerms x) n

  reciprocal : ℝ
  reciprocal =
    positiveReciprocal
      (1ℝ - x) positive-denominator

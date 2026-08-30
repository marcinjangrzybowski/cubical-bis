module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Sum.AbsBound where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Base using (fromNatℚ)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
  using (sub-zero-right)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
  using (mul-zero-right)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannSum.DyadicRecursive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Sum.Sub


-- A pointwise absolute error is amplified by at most the interval width,
-- independently of subdivision depth.  This is the operator-norm estimate
-- that makes the later two-limit argument possible.

dyadicRecursiveSum-pointwiseAbsBound :
  ∀ f g a b error n →
  (a≤b : a ≤ℝ b) →
  (∀ x → a ≤ℝ x → x ≤ℝ b →
    Abs.absℝ (f x Group.- g x) ≤ℝ error) →
  Abs.absℝ
    (dyadicRecursiveSum f a b n Group.-
      dyadicRecursiveSum g a b n)
  ≤ℝ (b Group.- a) Mul.· error
dyadicRecursiveSum-pointwiseAbsBound
  f g a b error n a≤b pointwise =
  subst
    (λ z → Abs.absℝ z ≤ℝ (b Group.- a) Mul.· error)
    path
    (dyadicRecursiveSum-constantAbsBound
      (λ x → f x Group.- g x) a b (Real.ιℚ 0) error n a≤b
      (λ x a≤x x≤b →
        subst
          (λ z → Abs.absℝ z ≤ℝ error)
          (sym (sub-zero-right (f x Group.- g x)))
          (pointwise x a≤x x≤b)))
  where
  path :
    dyadicRecursiveSum
      (λ x → f x Group.- g x) a b n Group.-
      (b Group.- a) Mul.· Real.ιℚ 0
    ≡
    dyadicRecursiveSum f a b n Group.-
      dyadicRecursiveSum g a b n
  path =
    cong
      (dyadicRecursiveSum
        (λ x → f x Group.- g x) a b n Group.-_)
      (mul-zero-right (b Group.- a))
    ∙ sub-zero-right
        (dyadicRecursiveSum (λ x → f x Group.- g x) a b n)
    ∙ dyadicRecursiveSum-sub f g a b n

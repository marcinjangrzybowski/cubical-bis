module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Sum.Sub where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannSum.DyadicRecursive


-- Recursive dyadic quadrature is linear before completion.  This exact
-- difference identity lets uniform errors be estimated structurally, once,
-- rather than by reasoning separately about every leaf of a flat partition.

dyadicRecursiveSum-sub : ∀ f g a b n →
  dyadicRecursiveSum (λ x → f x Group.- g x) a b n ≡
  dyadicRecursiveSum f a b n Group.-
  dyadicRecursiveSum g a b n
dyadicRecursiveSum-sub f g a b n =
  dyadicRecursiveSum-add f (Neg.-_ ∘ g) a b n
  ∙ cong (dyadicRecursiveSum f a b n Add.+_)
      (dyadicRecursiveSum-neg g a b n)

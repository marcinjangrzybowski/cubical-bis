module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.RationalModule where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.Module
open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Laws


-- The Cauchy-sequence reals form a rational vector space even though no
-- multiplication of two arbitrary completed points is used here.

ℝLeftℚModule : LeftModule (CommRing→Ring ℚCommRing) ℓ-zero
ℝLeftℚModule .fst = Real.ℝ
ℝLeftℚModule .snd .LeftModuleStr.0m = Real.ιℚ 0
ℝLeftℚModule .snd .LeftModuleStr._+_ = Add._+_
ℝLeftℚModule .snd .LeftModuleStr.-_ = Neg.-_
ℝLeftℚModule .snd .LeftModuleStr._⋆_ = Scalar._⋆_
ℝLeftℚModule .snd .LeftModuleStr.isLeftModule =
  makeIsLeftModule
    Real.Base.isSetCompletion add-assoc add-zero-right add-inverse-right add-comm
    scalar-assoc scalar-dist-right scalar-dist-left scalar-id

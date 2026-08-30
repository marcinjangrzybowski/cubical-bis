module Cubical.Analysis.Real.Algebra.Scalar.Structure where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.Module

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Laws


-- This structure depends only on additive real algebra and the independently
-- lifted rational action, not on multiplication of two arbitrary reals.

ℝLeftℚModule : LeftModule (CommRing→Ring ℚCommRing) ℓ-zero
ℝLeftℚModule .fst = ℝ
ℝLeftℚModule .snd .LeftModuleStr.0m = 0ℝ
ℝLeftℚModule .snd .LeftModuleStr._+_ = _+_
ℝLeftℚModule .snd .LeftModuleStr.-_ = -_
ℝLeftℚModule .snd .LeftModuleStr._⋆_ = _⋆_
ℝLeftℚModule .snd .LeftModuleStr.isLeftModule =
  makeIsLeftModule
    isSetℝ addAssoc addIdR addInvR addComm
    scalar-assoc scalar-dist-right scalar-dist-left scalar-id

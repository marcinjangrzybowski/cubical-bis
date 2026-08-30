module Cubical.Analysis.Real.Algebra.Scalar.Compatibility where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Scalar.Base


-- The independently lifted rational action agrees with multiplication by
-- the embedded rational in the completed commutative ring.

scalar-as-mul : ∀ c x → c ⋆ x ≡ rat c · x
scalar-as-mul c = funExt⁻
  (continuousExtensionality
    (c ⋆_) (rat c ·_)
    (scalar-isContinuous c) (mul-isContinuous₂ (rat c))
    λ q → scalar-rat c q ∙ sym (mul-rat c q))

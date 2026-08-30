module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Congruence.Sealed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws


opaque
  mul-cong₂-sealed : ∀ {a a' b b' : Real.ℝ} →
    a ≡ a' → b ≡ b' → a Mul.· b ≡ a' Mul.· b'
  mul-cong₂-sealed a≡a' b≡b' =
    cong₂ Mul._·_ a≡a' b≡b'


  mul-zero-right-sealed : ∀ x →
    x Mul.· Real.ιℚ 0 ≡ Real.ιℚ 0
  mul-zero-right-sealed = mul-zero-right


  mul-one-right-sealed : ∀ x →
    x Mul.· Real.ιℚ 1 ≡ x
  mul-one-right-sealed = mul-one-right

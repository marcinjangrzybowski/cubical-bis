module Cubical.Analysis.Complex.Norm.Difference where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
import Cubical.Analysis.Complex.Algebra.Identities as IdentitiesDefinition

private module C = IdentitiesDefinition.Identities ℂCommRing

normℂ-negativeDifference : ∀ z w → normℂ ((-ℂ z) -ℂ (-ℂ w)) ≡ normℂ (z -ℂ w)
normℂ-negativeDifference z w = cong normℂ (C.negativeDifference z w) ∙ normℂ-neg (z -ℂ w)

opaque
  normℂ-sumDifference : ∀ a b c d δ ε →
    normℂ (a -ℂ c) ≤ℝ δ → normℂ (b -ℂ d) ≤ℝ ε →
    normℂ ((a +ℂ b) -ℂ (c +ℂ d)) ≤ℝ δ + ε
  normℂ-sumDifference a b c d δ ε ac bd =
    subst (_≤ℝ δ + ε) (sym (cong normℂ (C.sumDifference a b c d)))
      (normℂ-addBound (a -ℂ c) (b -ℂ d) δ ε ac bd)

  normℂ-productDifference : ∀ a b c d A B δ ε →
    normℂ b ≤ℝ A → normℂ c ≤ℝ B →
    normℂ (a -ℂ c) ≤ℝ δ → normℂ (b -ℂ d) ≤ℝ ε →
    normℂ (a ·ℂ b -ℂ c ·ℂ d) ≤ℝ δ · A + B · ε
  normℂ-productDifference a b c d A B δ ε ba cb ac bd =
    subst (_≤ℝ δ · A + B · ε) (sym (cong normℂ (C.productDifference a b c d)))
      (normℂ-addBound ((a -ℂ c) ·ℂ b) (c ·ℂ (b -ℂ d)) (δ · A) (B · ε)
        (normℂ-mulBound (a -ℂ c) b δ A ac ba)
        (normℂ-mulBound c (b -ℂ d) B ε cb bd))

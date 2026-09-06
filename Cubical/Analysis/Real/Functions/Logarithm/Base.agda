module Cubical.Analysis.Real.Functions.Logarithm.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Functions.Exponential


-- Inverting a supplied equivalence needs no choice. These generic laws are
-- instantiated by Logarithm.Global using Exponential.Inverse's constructive
-- equivalence; their proofs remain independent of that construction.
opaque
  logarithmFromEquivalence : isEquiv expPositive → ℝ>0 → ℝ
  logarithmFromEquivalence equivalent = invEq (expPositive , equivalent)

  expPositive-logarithm : ∀ equivalent value →
    expPositive (logarithmFromEquivalence equivalent value) ≡ value
  expPositive-logarithm equivalent = secEq (expPositive , equivalent)

  logarithm-expPositive : ∀ equivalent x →
    logarithmFromEquivalence equivalent (expPositive x) ≡ x
  logarithm-expPositive equivalent = retEq (expPositive , equivalent)

  expℝ-logarithm : ∀ equivalent value →
    expℝ (logarithmFromEquivalence equivalent value) ≡ fst value
  expℝ-logarithm equivalent value =
    sym (expPositive-value (logarithmFromEquivalence equivalent value))
    ∙ cong fst (expPositive-logarithm equivalent value)

  logarithm-independent : ∀ (first second : isEquiv expPositive) value →
    logarithmFromEquivalence first value ≡ logarithmFromEquivalence second value
  logarithm-independent first second value =
    cong (λ equivalent → logarithmFromEquivalence equivalent value)
      (isPropIsEquiv expPositive first second)

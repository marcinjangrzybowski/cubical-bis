open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Limits
  {ℓ ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Properties

open PositiveRationals

module PM = PremetricStr (M' .snd)
module Theory = PremetricTheory M'


-- Cauchy convergence without a chosen modulus: the tail index is truncated
-- independently at each radius.

CauchyTail : (ℕ → M' .fst) → ℚ₊ → Type ℓ'
CauchyTail x ε =
  Σ[ N ∈ ℕ ]
    (∀ m n → N ℕ.≤ m → N ℕ.≤ n → x m PM.≈[ ε ] x n)

IsCauchySequence : (ℕ → M' .fst) → Type ℓ'
IsCauchySequence x = ∀ ε → ∥ CauchyTail x ε ∥₁

HasCauchySequenceLimits : Type (ℓ-max ℓ ℓ')
HasCauchySequenceLimits =
  ∀ x → IsCauchySequence x → Theory.limitSeq x

isPropHasCauchySequenceLimits : isProp HasCauchySequenceLimits
isPropHasCauchySequenceLimits =
  isPropΠ2 λ x _ → Theory.isPropLimitSeq x

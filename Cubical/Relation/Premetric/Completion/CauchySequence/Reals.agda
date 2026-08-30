module Cubical.Relation.Premetric.Completion.CauchySequence.Reals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion
import Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  as CompletionPremetric
import Cubical.Relation.Premetric.Completion.CauchySequence.Approximation
  as CompletionApproximation
import Cubical.Relation.Premetric.Completion.CauchySequence.Limits
  as CauchySequenceLimits

module Base = CauchyCompletion ℚPremetricSpace
module Premetric = CompletionPremetric ℚPremetricSpace
module Approximation = CompletionApproximation ℚPremetricSpace


-- The real numbers obtained by completing the rational premetric space with
-- Cauchy sequences.

ℝ : Type
ℝ = Base.Completion

ιℚ : ℚ → ℝ
ιℚ = Base.ι

ℝPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
ℝPremetricSpace = Premetric.CompletionPremetricSpace

module SequenceLimits = CauchySequenceLimits ℝPremetricSpace

isCompleteℝ : Premetric.CompletionTheory.isComplete
isCompleteℝ = Premetric.isCompleteCompletion

hasCauchySequenceLimitsℝ : SequenceLimits.HasCauchySequenceLimits
hasCauchySequenceLimitsℝ =
  Premetric.hasCauchySequenceLimitsCompletion


-- At each requested radius there merely exists a rational approximation.
-- This is the constructive density statement: it makes no simultaneous
-- choice of approximations at all radii.

rationalsDense : ∀ (x : ℝ) (ε : ℚ₊) →
  ∃[ q ∈ ℚ ] (ιℚ q Base.≈ᶜ[ ε ] x)
rationalsDense = Approximation.∃approx

rationalInjectionInjective : ∀ p q → ιℚ p ≡ ιℚ q → p ≡ q
rationalInjectionInjective = Approximation.isInjectiveι

-- The opposite orientation is equivalent by symmetry of the completion
-- premetric and is often the more convenient formulation of density.

rationalsDenseʳ : ∀ (x : ℝ) (ε : ℚ₊) →
  ∃[ q ∈ ℚ ] (x Base.≈ᶜ[ ε ] ιℚ q)
rationalsDenseʳ x ε = PT.map
  (λ { (q , ιq∼x) → q , Base.sym≈ᶜ (ιℚ q) x ε ιq∼x })
  (rationalsDense x ε)

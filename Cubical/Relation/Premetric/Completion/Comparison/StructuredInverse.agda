open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Comparison.StructuredInverse
  {ℓ ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Comparison
  as ComparisonDefinition

module Comparison = ComparisonDefinition M'
module Sequential = Comparison.Sequential
module SequentialMetric = Comparison.SequentialMetric
module RegularSequential = Comparison.RegularSequential
module CauchySequence = Comparison.CauchySequence
module CauchySequenceMetric = Comparison.CauchySequenceMetric


-- The canonical comparison is already available constructively.  It
-- forgets that a sequential Cauchy witness chooses all tail indices under
-- one truncation, retaining only a separately truncated tail at each
-- radius.

canonicalMap : Sequential.ℭ̂ₛ → CauchySequence.Completion
canonicalMap = fst Comparison.sequentialToCauchySequenceⁿ


CanonicalComparisonInvertible : Type (ℓ-max ℓ ℓ')
CanonicalComparisonInvertible = isEquiv canonicalMap


canonicalEquiv :
  CanonicalComparisonInvertible →
  Sequential.ℭ̂ₛ ≃ CauchySequence.Completion
canonicalEquiv invertible = canonicalMap , invertible


-- Bare invertibility supplies a point-valued inverse, but a point in the
-- sequential completion does not expose the witness used by one of its
-- `lim` constructors.  The additional structure below asks the inverse to
-- map a radiuswise Cauchy sequence to the native, bundled sequential
-- witness.  This is the witness component that appears in a genuine `lim`
-- computation rule.

CanonicalInversePreservesCauchy :
  CanonicalComparisonInvertible → Type (ℓ-max ℓ ℓ')
CanonicalInversePreservesCauchy invertible =
  ∀ x → CauchySequence.IsCauchySequence x →
    Sequential.SeqWitness (invEq (canonicalEquiv invertible) ∘ x)


isPropCanonicalInversePreservesCauchy : ∀ invertible →
  isProp (CanonicalInversePreservesCauchy invertible)
isPropCanonicalInversePreservesCauchy invertible =
  isPropΠ2 λ _ _ → squash₁


-- A structured inverse consists of invertibility of the fixed canonical
-- map together with precisely this Cauchy action.  No value-level `lim`
-- equation is required for the characterization below.

StructuredCanonicalInverse : Type (ℓ-max ℓ ℓ')
StructuredCanonicalInverse =
  Σ[ invertible ∈ CanonicalComparisonInvertible ]
    CanonicalInversePreservesCauchy invertible


isPropStructuredCanonicalInverse : isProp StructuredCanonicalInverse
isPropStructuredCanonicalInverse =
  isPropΣ (isPropIsEquiv canonicalMap)
    isPropCanonicalInversePreservesCauchy


-- Necessity --------------------------------------------------------------
--
-- Given a radiuswise Cauchy sequence `x` in the sequential completion, map
-- it forward pointwise.  Nonexpansiveness of the canonical map makes the
-- image radiuswise Cauchy.  The structured inverse supplies one bundled
-- witness for its inverse image, and the retraction law transports that
-- witness back to `x`.

structuredCanonicalInverse→tailChoice :
  StructuredCanonicalInverse → Comparison.SequentialTailChoice
structuredCanonicalInverse→tailChoice
    (invertible , preserves) x radiuswise =
  subst Sequential.SeqWitness round-trip
    (preserves lifted lifted-cauchy)
  where
  equivalence = canonicalEquiv invertible

  lifted : ℕ → CauchySequence.Completion
  lifted = canonicalMap ∘ x

  lifted-cauchy : CauchySequence.IsCauchySequence lifted
  lifted-cauchy ε = PT.map transport-tail (radiuswise ε)
    where
    transport-tail : Comparison.MiddleWitnesses.CauchyTail x ε →
      CauchySequence.CauchyTail lifted ε
    transport-tail (N , close) = N , λ m n N≤m N≤n →
      Comparison.sequentialToCauchySequenceⁿ
        .snd .IsNonExpanding.pres≈
          (x m) (x n) ε (close m n N≤m N≤n)

  round-trip : (invEq equivalence ∘ lifted) ≡ x
  round-trip = funExt λ n → retEq equivalence (x n)


-- Sufficiency ------------------------------------------------------------
--
-- Tail choice constructs the existing conditional inverse lift.  Its
-- nonexpansiveness first gives radiuswise Cauchyness of an inverse image
-- sequence; tail choice then bundles those radiuswise tails into the
-- `Sequential.SeqWitness` required above.

concreteInverse :
  Comparison.SequentialTailChoice →
  CauchySequence.Completion → Sequential.ℭ̂ₛ
concreteInverse choice =
  fst (Comparison.cauchySequenceToSequentialWithChoiceⁿ choice)


concreteInverse-section : ∀ choice y →
  canonicalMap (concreteInverse choice y) ≡ y
concreteInverse-section choice y =
  funExt⁻
    (cong fst
      (Comparison.regularAfterCauchySequenceWithChoiceⁿ choice)) y


concreteInverseRadiuswise :
  (choice : Comparison.SequentialTailChoice) →
  ∀ x → CauchySequence.IsCauchySequence x →
  Comparison.MiddleWitnesses.RadiuswiseCauchySequence
    (concreteInverse choice ∘ x)
concreteInverseRadiuswise choice x gx ε =
  PT.map transport-tail (gx ε)
  where
  transport-tail : CauchySequence.CauchyTail x ε →
    Comparison.MiddleWitnesses.CauchyTail
      (concreteInverse choice ∘ x) ε
  transport-tail (N , close) = N , λ m n N≤m N≤n →
    Comparison.cauchySequenceToSequentialWithChoiceⁿ choice
      .snd .IsNonExpanding.pres≈
        (x m) (x n) ε (close m n N≤m N≤n)


concreteInversePreservesCauchy :
  (choice : Comparison.SequentialTailChoice) →
  ∀ x → CauchySequence.IsCauchySequence x →
  Sequential.SeqWitness (concreteInverse choice ∘ x)
concreteInversePreservesCauchy choice x gx =
  choice (concreteInverse choice ∘ x)
    (concreteInverseRadiuswise choice x gx)


-- Tail choice also proves that the canonical map is invertible: compose
-- the unconditional sequential-to-regular equivalence with the conditional
-- regular-to-CauchySequence equivalence from `Comparison`.

concreteCanonicalEquiv :
  Comparison.SequentialTailChoice →
  Sequential.ℭ̂ₛ ≃ CauchySequence.Completion
concreteCanonicalEquiv choice =
  RegularSequential.sequentialRegularEquiv ∙ₑ
  Comparison.regularCauchySequenceEquivWithChoice choice


concreteCanonicalInvertible :
  Comparison.SequentialTailChoice → CanonicalComparisonInvertible
concreteCanonicalInvertible choice =
  concreteCanonicalEquiv choice .snd


-- Any inverse of a fixed equivalence is unique.  Consequently the concrete
-- inverse just constructed agrees with the inverse selected by an arbitrary
-- proof of invertibility of `canonicalMap`.

concreteInverse≡canonicalInverse :
  (invertible : CanonicalComparisonInvertible)
  (choice : Comparison.SequentialTailChoice) →
  concreteInverse choice ≡ invEq (canonicalEquiv invertible)
concreteInverse≡canonicalInverse invertible choice =
  funExt λ y →
    sym (retEq (canonicalEquiv invertible) (concreteInverse choice y))
    ∙ cong (invEq (canonicalEquiv invertible))
        (concreteInverse-section choice y)


tailChoice→canonicalInversePreservesCauchy :
  (invertible : CanonicalComparisonInvertible) →
  Comparison.SequentialTailChoice →
  CanonicalInversePreservesCauchy invertible
tailChoice→canonicalInversePreservesCauchy
    invertible choice x gx =
  subst Sequential.SeqWitness inverse-sequence
    (concreteInversePreservesCauchy choice x gx)
  where
  inverse-sequence :
    (concreteInverse choice ∘ x) ≡
    (invEq (canonicalEquiv invertible) ∘ x)
  inverse-sequence = funExt λ n →
    funExt⁻ (concreteInverse≡canonicalInverse invertible choice) (x n)


tailChoice→structuredCanonicalInverse :
  Comparison.SequentialTailChoice → StructuredCanonicalInverse
tailChoice→structuredCanonicalInverse choice =
  invertible ,
  tailChoice→canonicalInversePreservesCauchy invertible choice
  where
  invertible = concreteCanonicalInvertible choice


-- Exact characterization -------------------------------------------------
--
-- This is the promised necessary-and-sufficient statement.  It deliberately
-- concerns a structured inverse.  Bare `isEquiv canonicalMap` supplies a
-- point-valued inverse but does not expose the bundled witness demanded by
-- `Sequential.SeqWitness`; the second component of
-- `StructuredCanonicalInverse` records exactly that missing information.

structuredCanonicalInverse≃sequentialTailChoice :
  StructuredCanonicalInverse ≃ Comparison.SequentialTailChoice
structuredCanonicalInverse≃sequentialTailChoice =
  propBiimpl→Equiv
    isPropStructuredCanonicalInverse
    Comparison.isPropSequentialTailChoice
    structuredCanonicalInverse→tailChoice
    tailChoice→structuredCanonicalInverse


-- With a particular inverse already fixed, only its Cauchy action remains;
-- that action is itself equivalent to tail choice.

canonicalInversePreservesCauchy≃sequentialTailChoice :
  (invertible : CanonicalComparisonInvertible) →
  CanonicalInversePreservesCauchy invertible ≃
    Comparison.SequentialTailChoice
canonicalInversePreservesCauchy≃sequentialTailChoice invertible =
  propBiimpl→Equiv
    (isPropCanonicalInversePreservesCauchy invertible)
    Comparison.isPropSequentialTailChoice
    (structuredCanonicalInverse→tailChoice ∘ (invertible ,_))
    (tailChoice→canonicalInversePreservesCauchy invertible)

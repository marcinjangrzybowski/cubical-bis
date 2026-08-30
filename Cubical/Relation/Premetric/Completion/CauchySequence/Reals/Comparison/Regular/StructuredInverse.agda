module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular.StructuredInverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyRealsP.Foundation.Closeness as CR

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular
  as RegularComparison
import Cubical.Relation.Premetric.Completion.Comparison
  as ComparisonDefinition

module Comparison = ComparisonDefinition ℚPremetricSpace
module Sequential = Comparison.Sequential
module RegularSequential = Comparison.RegularSequential


-- This module states the tail-choice obstruction directly for the real
-- comparison already used by the algebraic development.  Its forward map
-- sends the usual regular Cauchy reals to the reals constructed with the
-- radiuswise Cauchy-sequence completion.

canonicalMap : CR.ℝ → Real.ℝ
canonicalMap = RegularComparison.fromRegular


CanonicalComparisonInvertible : Type₀
CanonicalComparisonInvertible = isEquiv canonicalMap


canonicalEquiv : CanonicalComparisonInvertible → CR.ℝ ≃ Real.ℝ
canonicalEquiv invertible = canonicalMap , invertible


-- The inverse lands in regular reals.  Applying the constructive
-- regular-to-sequential equivalence gives a sequence in the presentation
-- whose `lim` constructor expects one bundled Cauchy witness.  Requiring
-- that witness is the real-specific form of a Cauchy computation rule for
-- the inverse.

CanonicalInversePreservesCauchy :
  CanonicalComparisonInvertible → Type₀
CanonicalInversePreservesCauchy invertible =
  ∀ x → Real.Base.IsCauchySequence x →
    Sequential.SeqWitness
      (RegularSequential.fromRegular ∘
       invEq (canonicalEquiv invertible) ∘ x)


isPropCanonicalInversePreservesCauchy : ∀ invertible →
  isProp (CanonicalInversePreservesCauchy invertible)
isPropCanonicalInversePreservesCauchy invertible =
  isPropΠ2 λ _ _ → squash₁


StructuredCanonicalInverse : Type₀
StructuredCanonicalInverse =
  Σ[ invertible ∈ CanonicalComparisonInvertible ]
    CanonicalInversePreservesCauchy invertible


isPropStructuredCanonicalInverse : isProp StructuredCanonicalInverse
isPropStructuredCanonicalInverse =
  isPropΣ (isPropIsEquiv canonicalMap)
    isPropCanonicalInversePreservesCauchy


-- The sequential comparison factors through the regular reals.  Keeping
-- this equation explicit records why a structured inverse of `canonicalMap`
-- can be applied to the forward image of a sequential Cauchy sequence.

sequential-factorization :
  fst Comparison.sequentialToCauchySequenceⁿ ≡
  canonicalMap ∘ RegularSequential.toRegular
sequential-factorization = refl


-- Necessity --------------------------------------------------------------
--
-- Map a radiuswise Cauchy sequence of sequential reals into the new reals.
-- The canonical map is nonexpanding, so the image remains radiuswise
-- Cauchy.  The structured inverse supplies one bundled witness.  Its
-- retraction law, followed by the regular/sequential retraction, transports
-- that witness back to the original sequence.

structuredCanonicalInverse→tailChoice :
  StructuredCanonicalInverse → Comparison.SequentialTailChoice
structuredCanonicalInverse→tailChoice
    (invertible , preserves) x radiuswise =
  subst Sequential.SeqWitness round-trip
    (preserves lifted lifted-cauchy)
  where
  equivalence = canonicalEquiv invertible

  lifted : ℕ → Real.ℝ
  lifted = fst Comparison.sequentialToCauchySequenceⁿ ∘ x

  lifted-cauchy : Real.Base.IsCauchySequence lifted
  lifted-cauchy ε = PT.map transport-tail (radiuswise ε)
    where
    transport-tail : Comparison.MiddleWitnesses.CauchyTail x ε →
      Real.Base.CauchyTail lifted ε
    transport-tail (N , close) = N , λ m n N≤m N≤n →
      Comparison.sequentialToCauchySequenceⁿ
        .snd .IsNonExpanding.pres≈
          (x m) (x n) ε (close m n N≤m N≤n)

  round-trip :
    (RegularSequential.fromRegular ∘
     invEq equivalence ∘ lifted) ≡ x
  round-trip = funExt λ n →
    cong (RegularSequential.fromRegular ∘ invEq equivalence)
      (funExt⁻ sequential-factorization (x n))
    ∙ cong RegularSequential.fromRegular
        (retEq equivalence (RegularSequential.toRegular (x n)))
    ∙ retEq RegularSequential.sequentialRegularEquiv (x n)


-- Sufficiency ------------------------------------------------------------
--
-- Tail choice already constructs a nonexpanding inverse into regular
-- reals.  Composing it with the regular-to-sequential map preserves every
-- radiuswise Cauchy tail.  Tail choice then bundles these tails into the
-- witness required above.

concreteInverse :
  Comparison.SequentialTailChoice → Real.ℝ → CR.ℝ
concreteInverse choice =
  fst (Comparison.cauchySequenceToRegularWithChoiceⁿ choice)


concreteInverse-section : ∀ choice y →
  canonicalMap (concreteInverse choice y) ≡ y
concreteInverse-section choice y =
  funExt⁻
    (cong fst
      (Comparison.regularAfterCauchySequenceWithChoiceⁿ choice)) y


concreteSequentialInverseⁿ :
  Comparison.SequentialTailChoice →
  NE[ Real.ℝPremetricSpace , Comparison.SequentialMetric.ℭ̂ₛPremetricSpace ]
concreteSequentialInverseⁿ choice =
  Comparison.regularToSequentialⁿ ∘NE
  Comparison.cauchySequenceToRegularWithChoiceⁿ choice


concreteInverseRadiuswise :
  (choice : Comparison.SequentialTailChoice) →
  ∀ x → Real.Base.IsCauchySequence x →
  Comparison.MiddleWitnesses.RadiuswiseCauchySequence
    (fst (concreteSequentialInverseⁿ choice) ∘ x)
concreteInverseRadiuswise choice x gx ε =
  PT.map transport-tail (gx ε)
  where
  transport-tail : Real.Base.CauchyTail x ε →
    Comparison.MiddleWitnesses.CauchyTail
      (fst (concreteSequentialInverseⁿ choice) ∘ x) ε
  transport-tail (N , close) = N , λ m n N≤m N≤n →
    concreteSequentialInverseⁿ choice
      .snd .IsNonExpanding.pres≈
        (x m) (x n) ε (close m n N≤m N≤n)


concreteInversePreservesCauchy :
  (choice : Comparison.SequentialTailChoice) →
  ∀ x → Real.Base.IsCauchySequence x →
  Sequential.SeqWitness
    (RegularSequential.fromRegular ∘ concreteInverse choice ∘ x)
concreteInversePreservesCauchy choice x gx =
  choice (fst (concreteSequentialInverseⁿ choice) ∘ x)
    (concreteInverseRadiuswise choice x gx)


concreteCanonicalEquiv :
  Comparison.SequentialTailChoice → CR.ℝ ≃ Real.ℝ
concreteCanonicalEquiv =
  Comparison.regularCauchySequenceEquivWithChoice


concreteCanonicalInvertible :
  Comparison.SequentialTailChoice → CanonicalComparisonInvertible
concreteCanonicalInvertible choice =
  concreteCanonicalEquiv choice .snd


tailChoice→structuredCanonicalInverse :
  Comparison.SequentialTailChoice → StructuredCanonicalInverse
tailChoice→structuredCanonicalInverse choice =
  invertible , concreteInversePreservesCauchy choice
  where
  invertible = concreteCanonicalInvertible choice


-- Exact characterization -------------------------------------------------
--
-- Thus the standard real comparison has a structured inverse exactly when
-- radiuswise tails can be combined into the single witness expected by the
-- sequential limit constructor.  Bare invertibility is intentionally not
-- claimed sufficient: it gives inverse values, but not these witnesses.

structuredCanonicalInverse≃sequentialTailChoice :
  StructuredCanonicalInverse ≃ Comparison.SequentialTailChoice
structuredCanonicalInverse≃sequentialTailChoice =
  propBiimpl→Equiv
    isPropStructuredCanonicalInverse
    Comparison.isPropSequentialTailChoice
    structuredCanonicalInverse→tailChoice
    tailChoice→structuredCanonicalInverse


-- The usual propositional choice principle over positive rationals is a
-- sufficient corollary, while the equivalence above isolates the strictly
-- smaller tail-choice statement actually used by the real comparison.

positiveRationalChoice→structuredCanonicalInverse :
  Comparison.PositiveRationalChoice ℓ-zero →
  StructuredCanonicalInverse
positiveRationalChoice→structuredCanonicalInverse choice =
  tailChoice→structuredCanonicalInverse
    (Comparison.positiveRationalChoice→sequentialTailChoice choice)

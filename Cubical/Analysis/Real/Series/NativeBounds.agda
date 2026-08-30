module Cubical.Analysis.Real.Series.NativeBounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne using (ℕ₊₁)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Bounds
open import Cubical.Analysis.Real.Series.Absolute

open PositiveRationals


-- A bound packaged under truncation remains constructive: callers may
-- eliminate it only into propositions, rather than choosing a bound globally.

UniformRationalAbsBound : RealSequence → Type₀
UniformRationalAbsBound sequence =
  Σ[ bound ∈ ℚ₊ ]
    (∀ n → absℝ (sequence n) ≤ℝ rat (fst bound))


private
  subAddCancel : ∀ x y → (x - y) + y ≡ x
  subAddCancel x y =
    sym (addAssoc x (- y) y)
    ∙ cong (x +_) (addInvL y)
    ∙ addIdR x

  oneNonnegative : 0ℝ ≤ℝ 1ℝ
  oneNonnegative =
    subst (0ℝ ≤ℝ_) absOne (absNonnegative 1ℝ)


termLeAbsolutePartialSum : ∀ sequence n →
  absℝ (sequence n) ≤ℝ
  partialSum (absℝ ∘ sequence) (suc n)
termLeAbsolutePartialSum sequence n =
  subst
    (_≤ℝ partialSum (absℝ ∘ sequence) (suc n))
    (addIdL (absℝ (sequence n)))
    (addPres≤
      0ℝ (partialSum (absℝ ∘ sequence) n)
      (absℝ (sequence n)) (absℝ (sequence n))
      (partialSumNonnegative
        (absℝ ∘ sequence)
        (λ i → absNonnegative (sequence i)) n)
      (≤ℝ-refl (absℝ (sequence n))))


closeAtOne→absBound : ∀ x y →
  x ∼[ 1₊ ] y →
  absℝ x ≤ℝ 1ℝ + absℝ y
closeAtOne→absBound x y close =
  ≤ℝ-trans
    (absℝ x)
    (absℝ (x - y) + absℝ y)
    (1ℝ + absℝ y)
    (subst
      (_≤ℝ absℝ (x - y) + absℝ y)
      (cong absℝ (subAddCancel x y))
      (absTriangle (x - y) y))
    (addPres≤
      (absℝ (x - y)) 1ℝ
      (absℝ y) (absℝ y)
      (<ℝ-weaken
        (absℝ (x - y)) 1ℝ
        (closeness→absDifference< x y 1₊ close))
      (≤ℝ-refl (absℝ y)))


mereUniformRationalAbsBoundFromEnvelope : ∀ sequence envelope →
  (∀ n → absℝ (sequence n) ≤ℝ envelope) →
  ∥ UniformRationalAbsBound sequence ∥₁
mereUniformRationalAbsBoundFromEnvelope
    sequence envelope pointwise =
  PT.map fromNaturalBound (∃naturalUpperBound envelope)
  where
  fromNaturalBound :
    Σ[ n ∈ ℕ₊₁ ] envelope <ℝ rat (naturalRational n) →
    UniformRationalAbsBound sequence
  fromNaturalBound (n , envelope<n) =
    naturalBound n
    , λ k →
        ≤ℝ-trans
          (absℝ (sequence k)) envelope
          (rat (naturalRational n))
          (pointwise k)
          (<ℝ-weaken envelope
            (rat (naturalRational n)) envelope<n)


cauchyBoundCutoff : ∀ sequence →
  ChosenIsCauchySequence sequence → ℕ
cauchyBoundCutoff sequence chosen = fst chosen 1₊


cauchyBoundPrefix : ∀ sequence →
  ChosenIsCauchySequence sequence → ℝ
cauchyBoundPrefix sequence chosen =
  partialSum (absℝ ∘ sequence)
    (suc (cauchyBoundCutoff sequence chosen))


cauchyBoundTail : ∀ sequence →
  ChosenIsCauchySequence sequence → ℝ
cauchyBoundTail sequence chosen =
  1ℝ + absℝ (sequence (cauchyBoundCutoff sequence chosen))


cauchyBoundEnvelope : ∀ sequence →
  ChosenIsCauchySequence sequence → ℝ
cauchyBoundEnvelope sequence chosen =
  cauchyBoundPrefix sequence chosen
  + cauchyBoundTail sequence chosen


cauchyBoundPrefixNonnegative : ∀ sequence chosen →
  0ℝ ≤ℝ cauchyBoundPrefix sequence chosen
cauchyBoundPrefixNonnegative sequence chosen =
  partialSumNonnegative
    (absℝ ∘ sequence)
    (λ n → absNonnegative (sequence n))
    (suc (cauchyBoundCutoff sequence chosen))


cauchyBoundTailNonnegative : ∀ sequence chosen →
  0ℝ ≤ℝ cauchyBoundTail sequence chosen
cauchyBoundTailNonnegative sequence chosen =
  subst
    (_≤ℝ cauchyBoundTail sequence chosen)
    (addIdR 0ℝ)
    (addPres≤
      0ℝ 1ℝ 0ℝ
      (absℝ (sequence (cauchyBoundCutoff sequence chosen)))
      oneNonnegative
      (absNonnegative
        (sequence (cauchyBoundCutoff sequence chosen))))


cauchyBoundPrefix≤Envelope : ∀ sequence chosen →
  cauchyBoundPrefix sequence chosen ≤ℝ
  cauchyBoundEnvelope sequence chosen
cauchyBoundPrefix≤Envelope sequence chosen =
  subst
    (_≤ℝ cauchyBoundEnvelope sequence chosen)
    (addIdR (cauchyBoundPrefix sequence chosen))
    (addPres≤
      (cauchyBoundPrefix sequence chosen)
      (cauchyBoundPrefix sequence chosen)
      0ℝ (cauchyBoundTail sequence chosen)
      (≤ℝ-refl (cauchyBoundPrefix sequence chosen))
      (cauchyBoundTailNonnegative sequence chosen))


cauchyBoundTail≤Envelope : ∀ sequence chosen →
  cauchyBoundTail sequence chosen ≤ℝ
  cauchyBoundEnvelope sequence chosen
cauchyBoundTail≤Envelope sequence chosen =
  subst
    (_≤ℝ cauchyBoundEnvelope sequence chosen)
    (addIdL (cauchyBoundTail sequence chosen))
    (addPres≤
      0ℝ (cauchyBoundPrefix sequence chosen)
      (cauchyBoundTail sequence chosen)
      (cauchyBoundTail sequence chosen)
      (cauchyBoundPrefixNonnegative sequence chosen)
      (≤ℝ-refl (cauchyBoundTail sequence chosen)))


cauchyBoundBeforeCutoff : ∀ sequence chosen n →
  n ℕ.≤ cauchyBoundCutoff sequence chosen →
  absℝ (sequence n) ≤ℝ cauchyBoundEnvelope sequence chosen
cauchyBoundBeforeCutoff sequence chosen n before =
  ≤ℝ-trans
    (absℝ (sequence n))
    (cauchyBoundPrefix sequence chosen)
    (cauchyBoundEnvelope sequence chosen)
    (≤ℝ-trans
      (absℝ (sequence n))
      (partialSum (absℝ ∘ sequence) (suc n))
      (cauchyBoundPrefix sequence chosen)
      (termLeAbsolutePartialSum sequence n)
      (partialSumIndexMono
        (absℝ ∘ sequence)
        (λ i → absNonnegative (sequence i))
        (suc n) (suc (cauchyBoundCutoff sequence chosen))
        (ℕ.suc-≤-suc before)))
    (cauchyBoundPrefix≤Envelope sequence chosen)


cauchyBoundAfterCutoff : ∀ sequence chosen n →
  cauchyBoundCutoff sequence chosen ℕ.≤ n →
  absℝ (sequence n) ≤ℝ cauchyBoundEnvelope sequence chosen
cauchyBoundAfterCutoff sequence chosen n cutoff≤n =
  ≤ℝ-trans
    (absℝ (sequence n))
    (cauchyBoundTail sequence chosen)
    (cauchyBoundEnvelope sequence chosen)
    (closeAtOne→absBound
      (sequence n)
      (sequence (cauchyBoundCutoff sequence chosen))
      (snd chosen 1₊ n (cauchyBoundCutoff sequence chosen)
        cutoff≤n ℕ.≤-refl))
    (cauchyBoundTail≤Envelope sequence chosen)


chosenCauchyPointwiseEnvelope : ∀ sequence chosen n →
  absℝ (sequence n) ≤ℝ cauchyBoundEnvelope sequence chosen
chosenCauchyPointwiseEnvelope sequence chosen n =
  ℕ.≤CaseInduction
    {P = λ i _ →
      absℝ (sequence i) ≤ℝ cauchyBoundEnvelope sequence chosen}
    {n = n} {m = cauchyBoundCutoff sequence chosen}
    (cauchyBoundBeforeCutoff sequence chosen n)
    (cauchyBoundAfterCutoff sequence chosen n)


mereChosenCauchySequenceUniformRationalAbsBound :
  ∀ sequence →
  ChosenIsCauchySequence sequence →
  ∥ UniformRationalAbsBound sequence ∥₁
mereChosenCauchySequenceUniformRationalAbsBound sequence chosen =
  mereUniformRationalAbsBoundFromEnvelope
    sequence
    (cauchyBoundEnvelope sequence chosen)
    (chosenCauchyPointwiseEnvelope sequence chosen)

mereSeqWitnessUniformRationalAbsBound :
  ∀ sequence → SeqWitness sequence →
  ∥ UniformRationalAbsBound sequence ∥₁
mereSeqWitnessUniformRationalAbsBound sequence =
  PT.rec squash₁
    (mereChosenCauchySequenceUniformRationalAbsBound sequence)


mereCauchySeriesUniformPartialSumAbsBound :
  ∀ terms → IsCauchySeries terms →
  ∥ Σ[ bound ∈ ℚ₊ ]
      (∀ n →
        absℝ (partialSum terms n) ≤ℝ rat (fst bound))
  ∥₁
mereCauchySeriesUniformPartialSumAbsBound terms =
  mereSeqWitnessUniformRationalAbsBound (partialSum terms)


mereAbsolutelyCauchySeriesUniformAbsolutePartialSumBound :
  ∀ terms → IsAbsolutelyCauchySeries terms →
  ∥ Σ[ bound ∈ ℚ₊ ]
      (∀ n →
        partialSum (absℝ ∘ terms) n ≤ℝ rat (fst bound))
  ∥₁
mereAbsolutelyCauchySeriesUniformAbsolutePartialSumBound
    terms absolute =
  PT.map removeRedundantAbs
    (mereSeqWitnessUniformRationalAbsBound
      (partialSum (absℝ ∘ terms)) absolute)
  where
  removeRedundantAbs :
    UniformRationalAbsBound
      (partialSum (absℝ ∘ terms)) →
    Σ[ bound ∈ ℚ₊ ]
      (∀ n →
        partialSum (absℝ ∘ terms) n ≤ℝ rat (fst bound))
  removeRedundantAbs (bound , bounded) =
    bound
    , λ n →
        ≤ℝ-trans
          (partialSum (absℝ ∘ terms) n)
          (absℝ (partialSum (absℝ ∘ terms) n))
          (rat (fst bound))
          (leAbs (partialSum (absℝ ∘ terms) n))
          (bounded n)

module Cubical.HITs.CauchyReals.Complex.Analysis.Sequence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
  renaming (_≤_ to _≤ℕ_)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Properties
open OrderedCommRingTheory ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties

open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Completeness


module ℂP = PremetricTheory ℂPremetricSpace


ComplexSequence : Type₀
ComplexSequence = ℕ → ℂ


IsCauchySequenceℂ : ComplexSequence → Type₀
IsCauchySequenceℂ = ℂP.isCauchySeq


CauchyWitnessℂ : ComplexSequence → (ℚ₊ → ℕ) → Type₀
CauchyWitnessℂ sequence N =
  ∀ ε m n → N ε ≤ℕ m → N ε ≤ℕ n →
    sequence m ≈ℂ[ ε ] sequence n


ConvergesToℂ : ComplexSequence → ℂ → Type₀
ConvergesToℂ sequence limit =
  Σ[ N ∈ (ℚ₊ → ℕ) ]
    ((ε : ℚ₊) → (n : ℕ) → N ε ≤ℕ n →
      sequence n ≈ℂ[ ε ] limit)


ConvergenceWitnessℂ :
  ComplexSequence → ℂ → (ℚ₊ → ℕ) → Type₀
ConvergenceWitnessℂ sequence limit N =
  (ε : ℚ₊) → (n : ℕ) → N ε ≤ℕ n →
    sequence n ≈ℂ[ ε ] limit


HasComplexLimit : ComplexSequence → Type₀
HasComplexLimit sequence = Σ[ limit ∈ ℂ ] ConvergesToℂ sequence limit


cauchyApproximationFromModulus :
  ComplexSequence → (ℚ₊ → ℕ) → ℚ₊ → ℂ
cauchyApproximationFromModulus sequence N ε = sequence (N ε)


cauchyApproximationPackage : ∀ sequence → IsCauchySequenceℂ sequence →
  Σ[ approximation ∈ (ℚ₊ → ℂ) ] ℂP.isCauchy approximation
cauchyApproximationPackage sequence cauchy =
  ℂP.isCauchySeq→isCauchy sequence cauchy


cauchyApproximation : ∀ sequence → IsCauchySequenceℂ sequence → ℚ₊ → ℂ
cauchyApproximation sequence cauchy =
  fst (cauchyApproximationPackage sequence cauchy)


opaque
  cauchyApproximation-left :
    (sequence : ComplexSequence) (N : ℚ₊ → ℕ)
    (cauchy : CauchyWitnessℂ sequence N)
    (ε δ : ℚ₊) →
    sequence (N ε) ≈ℂ[ ε ] sequence (ℕ.max (N ε) (N δ))
  cauchyApproximation-left sequence N cauchy ε δ =
    cauchy ε (N ε) (ℕ.max (N ε) (N δ))
      ℕ.≤-refl (ℕ.left-≤-max {N ε} {N δ})


opaque
  cauchyApproximation-right :
    (sequence : ComplexSequence) (N : ℚ₊ → ℕ)
    (cauchy : CauchyWitnessℂ sequence N)
    (ε δ : ℚ₊) →
    sequence (ℕ.max (N ε) (N δ)) ≈ℂ[ δ ] sequence (N δ)
  cauchyApproximation-right sequence N cauchy ε δ =
    cauchy δ (ℕ.max (N ε) (N δ)) (N δ)
      (ℕ.right-≤-max {N δ} {N ε}) ℕ.≤-refl


opaque
  cauchyApproximation-close :
    (sequence : ComplexSequence) (N : ℚ₊ → ℕ)
    (cauchy : CauchyWitnessℂ sequence N)
    (ε δ : ℚ₊) →
    sequence (N ε) ≈ℂ[ ε +₊ δ ] sequence (N δ)
  cauchyApproximation-close sequence N cauchy ε δ =
    PremetricStr.isTriangular≈ (snd ℂPremetricSpace)
      (sequence (N ε)) (sequence (ℕ.max (N ε) (N δ)))
      (sequence (N δ)) ε δ
      (cauchyApproximation-left sequence N cauchy ε δ)
      (cauchyApproximation-right sequence N cauchy ε δ)

complexSequenceLimitPackage : ∀ sequence cauchy →
  ℂP.limit (fst (cauchyApproximationPackage sequence cauchy))
complexSequenceLimitPackage sequence cauchy =
  isCompleteℂ
    (fst (cauchyApproximationPackage sequence cauchy))
    (snd (cauchyApproximationPackage sequence cauchy))


complexSequenceLimit : ∀ sequence → IsCauchySequenceℂ sequence → ℂ
complexSequenceLimit sequence cauchy = fst
  (complexSequenceLimitPackage sequence cauchy)


opaque
  complexSequenceLimitIsLimit : ∀ sequence cauchy →
    ℂP.isLimit
      (fst (cauchyApproximationPackage sequence cauchy))
      (fst (complexSequenceLimitPackage sequence cauchy))
  complexSequenceLimitIsLimit sequence cauchy = snd
    (complexSequenceLimitPackage sequence cauchy)

cauchySequenceIndex : ∀ sequence →
  IsCauchySequenceℂ sequence → ℚ₊ → ℕ
cauchySequenceIndex sequence cauchy ε =
  fst cauchy (ε /4₊)


sequenceNearApproximationAt :
  (sequence : ComplexSequence) (N : ℚ₊ → ℕ)
  (cauchy : CauchyWitnessℂ sequence N) (θ : ℚ₊) (n : ℕ) →
  N θ ≤ℕ n → sequence n ≈ℂ[ θ ] sequence (N θ)
sequenceNearApproximationAt sequence N cauchy θ n N≤n =
  cauchy θ n (N θ) N≤n (ℕ.≤-refl {N θ})

opaque
  cauchyApproximation-at :
    (sequence : ComplexSequence) (N : ℚ₊ → ℕ)
    (cauchy : CauchyWitnessℂ sequence N) (ε : ℚ₊) →
    fst (cauchyApproximationPackage sequence (N , cauchy)) ε ≡
      sequence (N ε)
  cauchyApproximation-at sequence N cauchy ε = refl

opaque
  approximationNearLimit :
    (sequence : ComplexSequence) (N : ℚ₊ → ℕ)
    (cauchy : CauchyWitnessℂ sequence N) (θ : ℚ₊) →
    sequence (N θ) ≈ℂ[ θ +₊ θ ]
      fst (complexSequenceLimitPackage sequence (N , cauchy))
  approximationNearLimit sequence N cauchy θ =
    subst
      (_≈ℂ[ θ +₊ θ ]
        fst (complexSequenceLimitPackage sequence (N , cauchy)))
      (cauchyApproximation-at sequence N cauchy θ)
      (complexSequenceLimitIsLimit sequence (N , cauchy) θ θ)


opaque
  sequenceNearLimitAtTripleRadius :
    (sequence : ComplexSequence) (N : ℚ₊ → ℕ)
    (cauchy : CauchyWitnessℂ sequence N) (θ : ℚ₊) (n : ℕ) →
    N θ ≤ℕ n →
    sequence n ≈ℂ[ θ +₊ (θ +₊ θ) ]
      fst (complexSequenceLimitPackage sequence (N , cauchy))
  sequenceNearLimitAtTripleRadius sequence N cauchy θ n N≤n =
    PremetricStr.isTriangular≈ (snd ℂPremetricSpace)
      (sequence n)
      (sequence (N θ))
      (fst (complexSequenceLimitPackage sequence (N , cauchy)))
      θ (θ +₊ θ)
      (sequenceNearApproximationAt sequence N cauchy θ n N≤n)
      (approximationNearLimit sequence N cauchy θ)


opaque
  tripleQuarter< : ∀ ε →
    (ε /4₊) +₊ ((ε /4₊) +₊ (ε /4₊)) <₊ ε
  tripleQuarter< ε = <≤ℚ!


opaque
  cauchySequenceNearLimit :
    (sequence : ComplexSequence) (N : ℚ₊ → ℕ)
    (cauchy : CauchyWitnessℂ sequence N) (ε : ℚ₊) (n : ℕ) →
    N (ε /4₊) ≤ℕ n →
    sequence n ≈ℂ[ ε ]
      fst (complexSequenceLimitPackage sequence (N , cauchy))
  cauchySequenceNearLimit sequence N cauchy ε n N≤n =
    PremetricStr.isMonotone≈< (snd ℂPremetricSpace)
      (sequence n)
      (fst (complexSequenceLimitPackage sequence (N , cauchy)))
      ((ε /4₊) +₊ ((ε /4₊) +₊ (ε /4₊))) ε
      (tripleQuarter< ε)
      (sequenceNearLimitAtTripleRadius sequence N cauchy
        (ε /4₊) n N≤n)

cauchySequenceConverges : ∀ sequence cauchy →
  ConvergesToℂ sequence
    (fst (complexSequenceLimitPackage sequence cauchy))
cauchySequenceConverges sequence (N , cauchy) =
  (λ ε → N (ε /4₊)) ,
  cauchySequenceNearLimit sequence N cauchy


cauchySequenceHasLimit : ∀ sequence →
  IsCauchySequenceℂ sequence → HasComplexLimit sequence
cauchySequenceHasLimit sequence cauchy =
  fst (complexSequenceLimitPackage sequence cauchy) ,
  cauchySequenceConverges sequence cauchy


opaque
  leftLimitNearCommonTerm :
    (sequence : ComplexSequence) (l : ℂ) (N : ℚ₊ → ℕ)
    (converges-l : ConvergenceWitnessℂ sequence l N)
    (M : ℚ₊ → ℕ) (θ : ℚ₊) →
    l ≈ℂ[ θ ] sequence (ℕ.max (N θ) (M θ))
  leftLimitNearCommonTerm sequence l N converges-l M θ =
    PremetricStr.isSym≈ (snd ℂPremetricSpace)
      (sequence (ℕ.max (N θ) (M θ))) l θ
      (converges-l θ (ℕ.max (N θ) (M θ))
        (ℕ.left-≤-max {N θ} {M θ}))


opaque
  commonTermNearRightLimit :
    (sequence : ComplexSequence) (m : ℂ) (M : ℚ₊ → ℕ)
    (converges-m : ConvergenceWitnessℂ sequence m M)
    (N : ℚ₊ → ℕ) (θ : ℚ₊) →
    sequence (ℕ.max (N θ) (M θ)) ≈ℂ[ θ ] m
  commonTermNearRightLimit sequence m M converges-m N θ =
    converges-m θ (ℕ.max (N θ) (M θ))
      (ℕ.right-≤-max {M θ} {N θ})


opaque
  limitsNearAtDoubleRadius :
    (sequence : ComplexSequence) (l m : ℂ)
    (N : ℚ₊ → ℕ) (converges-l : ConvergenceWitnessℂ sequence l N)
    (M : ℚ₊ → ℕ) (converges-m : ConvergenceWitnessℂ sequence m M)
    (θ : ℚ₊) → l ≈ℂ[ θ +₊ θ ] m
  limitsNearAtDoubleRadius sequence l m N converges-l M converges-m θ =
    PremetricStr.isTriangular≈ (snd ℂPremetricSpace)
      l (sequence (ℕ.max (N θ) (M θ))) m θ θ
      (leftLimitNearCommonTerm sequence l N converges-l M θ)
      (commonTermNearRightLimit sequence m M converges-m N θ)


opaque
  complexSequenceLimitUnique : ∀ sequence l m →
    ConvergesToℂ sequence l → ConvergesToℂ sequence m → l ≡ m
  complexSequenceLimitUnique sequence l m (N , converges-l)
    (M , converges-m) =
    PremetricStr.isSeparated≈ (snd ℂPremetricSpace) l m λ (ε : ℚ₊) →
      PremetricStr.subst≈ (snd ℂPremetricSpace) l m
        {ε = (ε /2₊) +₊ (ε /2₊)} {ε' = ε}
        (1/2∈ℚ./2+/2≡id (fst ε))
        (limitsNearAtDoubleRadius sequence l m
          N converges-l M converges-m (ε /2₊))

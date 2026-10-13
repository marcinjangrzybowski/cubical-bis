module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Characterization where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Order.Sequence
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Definition
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Iteration
  renaming (dampedBishopPiHalfApproximation to d)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Bounds
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.CosineZero

private
  opaque
    -- A single radius, supplied by the strict gap, suffices to find an
    -- approximation above x. No family of tail indices is selected.
    nearAbove : ∀ x y z (δ : ℚ₊) → x + rat (fst δ) ≤ℝ y →
      z ∼[ δ ] y → x <ℝ z
    nearAbove x y z δ gap close = <ℝ-addR-cancel x z (rat (fst δ))
      (≤<ℝ-trans (x + rat (fst δ)) y (z + rat (fst δ)) gap
        (subst2 _<ℝ_ (subAddCancel y z) (addComm (rat (fst δ)) z)
          (<ℝ-addR (y - z) (rat (fst δ)) z
            (≤<ℝ-trans (y - z) (absℝ (y - z)) (rat (fst δ))
              (leAbs (y - z))
              (subst (_<ℝ rat (fst δ)) (absSubComm z y)
                (closeness→absDifference< z y δ close))))))

  opaque
    pointAbove : ∀ sequence l → isLimitSequence sequence l →
      ∀ x → x <ℝ l → ∃[ n ∈ ℕ ] x <ℝ sequence n
    pointAbove sequence l converges x = PT.rec squash₁ fromGap
      where
      fromGap : PositiveGap x l → ∃[ n ∈ ℕ ] x <ℝ sequence n
      fromGap (δ , gap) = PT.map
        (λ (N , tail) → N , nearAbove x l (sequence N) δ gap (tail N ℕ.≤-refl))
        (converges δ)

  opaque
    candidatePositive : (candidate : DampedBishopPiHalfLimit) → 0ℝ <ℝ fst candidate
    candidatePositive candidate = <≤ℝ-trans 0ℝ damping (fst candidate) damping-positive
      (limitsPres≤ (λ _ → damping) (λ n → d (suc n)) damping (fst candidate)
        (constantIsLimitSequence damping)
        (shiftPresIsLimitSequence 1 d (fst candidate) (snd candidate))
        dampedBishopAfterFirst)

  opaque
    candidatePositiveBefore : (candidate : DampedBishopPiHalfLimit) →
      ∀ x → 0ℝ ≤ℝ x → x <ℝ fst candidate → 0ℝ <ℝ cosℝ x
    candidatePositiveBefore candidate x nonnegative below = PT.rec (isProp<ℝ 0ℝ (cosℝ x))
      (λ (n , x<dn) → <≤ℝ-trans 0ℝ (cosℝ (d n)) (cosℝ x)
        (fst (snd (dampedBishopPrefix n)))
        (snd (snd (dampedBishopPrefix n)) x nonnegative (<ℝ-weaken x (d n) x<dn)))
      (pointAbove d (fst candidate) (snd candidate) x below)

  opaque
    candidateCharacterization : (candidate : DampedBishopPiHalfLimit) →
      IsFirstPositiveCosineZero (fst candidate)
    candidateCharacterization candidate = candidatePositive candidate ,
      subst {x = dampedBishopPiHalfCandidate candidate} {y = fst candidate}
        (λ z → cosℝ z ≡ 0ℝ) refl (dampedBishopPiHalfLimit-cosineZero candidate) ,
      candidatePositiveBefore candidate

opaque
  dampedBishopLimit-characterization : IsFirstPositiveCosineZero (fst dampedBishopPiHalfLimit)
  dampedBishopLimit-characterization = candidateCharacterization dampedBishopPiHalfLimit

-- This inhabits the existing proof-independent specification with the
-- native sequential limit of the damped Bishop recurrence.
dampedBishopHalfPi : CharacterizedHalfPi
dampedBishopHalfPi = fst dampedBishopPiHalfLimit , dampedBishopLimit-characterization

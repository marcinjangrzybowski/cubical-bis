module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Iteration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Rationals.Base as ℚ using (ℚ)

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open 1/2∈ℚ using (_/2)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Series.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


-- A damped form of Bishop's cosine iteration.  The rational half-step is
-- kept explicit so later convergence estimates can refer to the damping
-- coefficient without normalizing completed multiplication.

dampedBishopCoefficient : ℚ
dampedBishopCoefficient = ℚ.fromNat 1 /2


dampedBishopPiHalfApproximation : ℕ → ℝ
dampedBishopPiHalfApproximation zero = 0ℝ
dampedBishopPiHalfApproximation (suc n) =
  dampedBishopPiHalfApproximation n +
    dampedBishopCoefficient ⋆
      cosℝ (dampedBishopPiHalfApproximation n)


dampedBishopPiHalfApproximation-zero :
  dampedBishopPiHalfApproximation zero ≡ 0ℝ
dampedBishopPiHalfApproximation-zero = refl


dampedBishopPiHalfApproximation-step : ∀ n →
  dampedBishopPiHalfApproximation (suc n)
    ≡
  dampedBishopPiHalfApproximation n +
    dampedBishopCoefficient ⋆
      cosℝ (dampedBishopPiHalfApproximation n)
dampedBishopPiHalfApproximation-step n = refl


dampedBishopPiHalfTerms : ℕ → ℝ
dampedBishopPiHalfTerms =
  (dampedBishopCoefficient ⋆_) ∘
    cosℝ ∘ dampedBishopPiHalfApproximation


opaque
  dampedBishopPiHalfApproximation-difference : ∀ n →
    dampedBishopPiHalfApproximation (suc n) -
      dampedBishopPiHalfApproximation n
      ≡
    dampedBishopPiHalfTerms n
  dampedBishopPiHalfApproximation-difference n =
      sym
        (addAssoc
          (dampedBishopPiHalfApproximation n)
          (dampedBishopPiHalfTerms n)
          (- dampedBishopPiHalfApproximation n))
    ∙ cong (dampedBishopPiHalfApproximation n +_)
        (addComm
          (dampedBishopPiHalfTerms n)
          (- dampedBishopPiHalfApproximation n))
    ∙ addAssoc
        (dampedBishopPiHalfApproximation n)
        (- dampedBishopPiHalfApproximation n)
        (dampedBishopPiHalfTerms n)
    ∙ cong (_+ dampedBishopPiHalfTerms n)
        (addInvR (dampedBishopPiHalfApproximation n))
    ∙ addIdL (dampedBishopPiHalfTerms n)


opaque
  dampedBishopPiHalfApproximation-asPartialSum : ∀ n →
    dampedBishopPiHalfApproximation n
      ≡
    partialSum dampedBishopPiHalfTerms n
  dampedBishopPiHalfApproximation-asPartialSum zero = refl
  dampedBishopPiHalfApproximation-asPartialSum (suc n) =
    cong
      (_+ dampedBishopPiHalfTerms n)
      (dampedBishopPiHalfApproximation-asPartialSum n)

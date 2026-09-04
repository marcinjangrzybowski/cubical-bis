module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Iteration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ; zero; suc)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Series.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


-- Bishop's constructive construction approaches pi/2 by repeatedly adding
-- the current cosine.  Its convergence proof is deliberately kept separate:
-- it is the analytic core that uses first-quadrant positivity and a geometric
-- contraction estimate.

bishopPiHalfApproximation : ℕ → ℝ
bishopPiHalfApproximation zero = 0ℝ
bishopPiHalfApproximation (suc n) =
  bishopPiHalfApproximation n +
    cosℝ (bishopPiHalfApproximation n)


bishopPiHalfApproximation-zero :
  bishopPiHalfApproximation zero ≡ 0ℝ
bishopPiHalfApproximation-zero = refl


bishopPiHalfApproximation-step : ∀ n →
  bishopPiHalfApproximation (suc n)
    ≡
  bishopPiHalfApproximation n +
    cosℝ (bishopPiHalfApproximation n)
bishopPiHalfApproximation-step n = refl


bishopPiHalfCosineTerms : ℕ → ℝ
bishopPiHalfCosineTerms =
  cosℝ ∘ bishopPiHalfApproximation


opaque
  bishopPiHalfApproximation-difference : ∀ n →
    bishopPiHalfApproximation (suc n) -
      bishopPiHalfApproximation n
      ≡
    cosℝ (bishopPiHalfApproximation n)
  bishopPiHalfApproximation-difference n =
      sym
        (addAssoc
        (bishopPiHalfApproximation n)
        (cosℝ (bishopPiHalfApproximation n))
        (- bishopPiHalfApproximation n))
    ∙ cong (bishopPiHalfApproximation n +_)
        (addComm
          (cosℝ (bishopPiHalfApproximation n))
          (- bishopPiHalfApproximation n))
    ∙ addAssoc
          (bishopPiHalfApproximation n)
          (- bishopPiHalfApproximation n)
          (cosℝ (bishopPiHalfApproximation n))
    ∙ cong (_+ cosℝ (bishopPiHalfApproximation n))
        (addInvR (bishopPiHalfApproximation n))
    ∙ addIdL (cosℝ (bishopPiHalfApproximation n))


opaque
  bishopPiHalfApproximation-asPartialSum : ∀ n →
    bishopPiHalfApproximation n
      ≡
    partialSum bishopPiHalfCosineTerms n
  bishopPiHalfApproximation-asPartialSum zero = refl
  bishopPiHalfApproximation-asPartialSum (suc n) =
    cong
      (_+ cosℝ (bishopPiHalfApproximation n))
      (bishopPiHalfApproximation-asPartialSum n)

module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.CosineZero where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base using (ℚ)
import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open 1/2∈ℚ using (/2+/2≡id)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ; addIdL)
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Laws
open import Cubical.Analysis.Real.Sequence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Iteration
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Terms
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Image


opaque
  dampedHalfScalar-cancelZero : ∀ x →
    dampedBishopCoefficient ⋆ x ≡ 0ℝ →
    x ≡ 0ℝ
  dampedHalfScalar-cancelZero x scaled-zero =
      sym (scalar-id x)
    ∙ cong (_⋆ x) (sym (/2+/2≡id (ℚ.fromNat 1)))
    ∙ scalar-dist-left
        dampedBishopCoefficient dampedBishopCoefficient x
    ∙ cong₂ _+_ scaled-zero scaled-zero
    ∙ addIdL 0ℝ


opaque
  dampedBishopPiHalfLimit-scaledCosineZero :
    (candidate : DampedBishopPiHalfLimit) →
    dampedBishopCoefficient ⋆
      cosℝ (dampedBishopPiHalfCandidate candidate)
      ≡ 0ℝ
  dampedBishopPiHalfLimit-scaledCosineZero candidate =
    cong fst
      (isPropSequenceLimit dampedBishopPiHalfTerms
        ( dampedBishopCoefficient ⋆
            cosℝ (dampedBishopPiHalfCandidate candidate)
        , dampedBishopPiHalfTerms→candidateScaledCosine candidate
        )
        (0ℝ , dampedBishopPiHalfTerms→zero candidate))


  dampedBishopPiHalfLimit-cosineZero :
    (candidate : DampedBishopPiHalfLimit) →
    cosℝ (dampedBishopPiHalfCandidate candidate) ≡ 0ℝ
  dampedBishopPiHalfLimit-cosineZero candidate =
    dampedHalfScalar-cancelZero
      (cosℝ (dampedBishopPiHalfCandidate candidate))
      (dampedBishopPiHalfLimit-scaledCosineZero candidate)

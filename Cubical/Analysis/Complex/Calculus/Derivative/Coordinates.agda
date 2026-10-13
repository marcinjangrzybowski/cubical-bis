module Cubical.Analysis.Complex.Calculus.Derivative.Coordinates where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (0≤→isNonnegative)
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Strict.Slack using (positiveSlack)
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.SmallError

-- A real coordinate remainder is small relative to the full complex
-- displacement. This does not assert holomorphicity of a coordinate map.
realCoordinateRemainder : (ℂ → ℝ) → (ℝ → ℝ) → ℝ → ℂ → ℂ → ℂ
realCoordinateRemainder coordinate f d z w =
  fromℝ ((f (coordinate w) - f (coordinate z)) - d · (coordinate w - coordinate z))

private
  opaque
    coordinateRemainderSmall : (coordinate : ℂ → ℝ) →
      (∀ z w ε → z ∼ℂ[ ε ] w → coordinate z ∼[ ε ] coordinate w) →
      (∀ z w → absℝ (coordinate w - coordinate z) ≤ℝ normℂ (w -ℂ z)) →
      ∀ f d z → IsDerivativeAt f d (coordinate z) →
      IsSmallComplexErrorAt (ℂPremetricSpace .snd) z (λ w → w -ℂ z)
        (realCoordinateRemainder coordinate f d z)
    coordinateRemainderSmall coordinate preserves bounded f d z differentiable ε =
      PT.map combine (differentiable ε)
      where
      combine :
        (Σ[ δ ∈ ℚ₊ ] (∀ t → coordinate z ∼[ δ ] t →
          absℝ ((f t - f (coordinate z)) - d · (t - coordinate z))
            ≤ℝ rat (fst ε) · absℝ (t - coordinate z))) →
        (Σ[ δ ∈ ℚ₊ ] (∀ w → z ∼ℂ[ δ ] w →
          normℂ (realCoordinateRemainder coordinate f d z w) ≤ℝ rat (fst ε) · normℂ (w -ℂ z)))
      combine (δ , near) = δ , λ w close →
        subst (_≤ℝ rat (fst ε) · normℂ (w -ℂ z))
          (sym (normℂ-fromℝ ((f (coordinate w) - f (coordinate z)) - d · (coordinate w - coordinate z))))
          (≤ℝ-trans (absℝ ((f (coordinate w) - f (coordinate z)) - d · (coordinate w - coordinate z)))
            (rat (fst ε) · absℝ (coordinate w - coordinate z)) (rat (fst ε) · normℂ (w -ℂ z))
            (near (coordinate w) (preserves z w δ close))
            (mulPres≤L (absℝ (coordinate w - coordinate z)) (normℂ (w -ℂ z)) (rat (fst ε))
              (0≤→isNonnegative (rat (fst ε)) (<ℝ-weaken 0ℝ (rat (fst ε)) (positiveSlack ε))) (bounded z w)))

realDerivativeRealCoordinateErrorSmallAt : ∀ f d z → IsDerivativeAt f d (re z) →
  IsSmallComplexErrorAt (ℂPremetricSpace .snd) z (λ w → w -ℂ z) (realCoordinateRemainder re f d z)
realDerivativeRealCoordinateErrorSmallAt = coordinateRemainderSmall re (λ _ _ _ → fst)
  (λ z w → reAbs≤normℂ (w -ℂ z))

realDerivativeImaginaryCoordinateErrorSmallAt : ∀ f d z → IsDerivativeAt f d (im z) →
  IsSmallComplexErrorAt (ℂPremetricSpace .snd) z (λ w → w -ℂ z) (realCoordinateRemainder im f d z)
realDerivativeImaginaryCoordinateErrorSmallAt = coordinateRemainderSmall im (λ _ _ _ → snd)
  (λ z w → imAbs≤normℂ (w -ℂ z))

opaque
  -- Widening the controlling displacement uses only a pointwise norm bound.
  smallComplexErrorLargerDisplacement : ∀ z (first second error : ℂ → ℂ) →
    (∀ w → normℂ (first w) ≤ℝ normℂ (second w)) →
    IsSmallComplexErrorAt (ℂPremetricSpace .snd) z first error →
    IsSmallComplexErrorAt (ℂPremetricSpace .snd) z second error
  smallComplexErrorLargerDisplacement z first second error bounded small ε = PT.map
    (λ { (δ , near) → δ , λ w close →
      ≤ℝ-trans (normℂ (error w)) (rat (fst ε) · normℂ (first w)) (rat (fst ε) · normℂ (second w))
        (near w close) (mulPres≤L (normℂ (first w)) (normℂ (second w)) (rat (fst ε))
          (0≤→isNonnegative (rat (fst ε)) (<ℝ-weaken 0ℝ (rat (fst ε)) (positiveSlack ε))) (bounded w)) }) (small ε)

  realDisplacementNormBound : ∀ z w → normℂ (fromℝ (re w - re z)) ≤ℝ normℂ (w -ℂ z)
  realDisplacementNormBound z w = subst (_≤ℝ normℂ (w -ℂ z))
    (sym (normℂ-fromℝ (re w - re z))) (reAbs≤normℂ (w -ℂ z))

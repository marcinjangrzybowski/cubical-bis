module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Estimates where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Geometric
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.SharpBounds
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Bounds

private
  module R = RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  opaque
    addedIncrement : ∀ x t → (x + t) - x ≡ t
    addedIncrement x t = cong (_+ (- x)) (addComm x t) ∙ R.plusMinus t x

-- Keep the sequence and its recurrence abstract while checking estimates.
module Estimates (sequence : ℕ → ℝ)
  (start : sequence zero ≡ 0ℝ)
  (first : sequence (suc zero) ≡ damping)
  (next : ∀ n → sequence (suc n) ≡ step (sequence n))
  (prefix : ∀ n → CosinePrefix (sequence n))
  (increasing : ∀ n → sequence n ≤ℝ sequence (suc n))
  (afterFirst : ∀ n → damping ≤ℝ sequence (suc n)) where

  opaque
    cosineContracts : ∀ n →
      cosℝ (sequence (suc (suc n))) ≤ℝ contraction · cosℝ (sequence (suc n))
    cosineContracts n = subst {x = step (sequence (suc n))} {y = sequence (suc (suc n))}
      (λ y → cosℝ y ≤ℝ contraction · cosℝ (sequence (suc n)))
      (sym (next (suc n)))
      (step-contracts (sequence (suc n)) (prefix (suc n)) (afterFirst n))

  opaque
    cosineGeometric : ∀ n →
      cosℝ (sequence (suc n)) ≤ℝ cosℝ (sequence (suc zero)) · powℝ contraction n
    cosineGeometric = contractionGeometricBound
      (λ n → cosℝ (sequence (suc n))) contraction contraction-nonnegative cosineContracts
  opaque
    increment : ∀ n → successiveIncrements sequence n ≡ damping · cosℝ (sequence n)
    increment n = subst {x = step (sequence n)} {y = sequence (suc n)}
      (λ y → y - sequence n ≡ damping · cosℝ (sequence n))
      (sym (next n)) (addedIncrement (sequence n) (damping · cosℝ (sequence n)))

  opaque
    absIncrement : ∀ n → absℝ (successiveIncrements sequence n) ≡ damping · cosℝ (sequence n)
    absIncrement n =
      absOfNonnegative (successiveIncrements sequence n)
        (nonnegativeSub (sequence n) (sequence (suc n)) (increasing n))
      ∙ increment n
  opaque
    leadingBound : damping · cosℝ (sequence (suc zero)) ≤ℝ contraction
    leadingBound = ≤ℝ-trans (damping · cosℝ (sequence (suc zero))) damping contraction
      (subst {x = damping · 1ℝ} {y = damping}
        (damping · cosℝ (sequence (suc zero)) ≤ℝ_) (mulIdR damping)
        (mulPres≤L (cosℝ (sequence (suc zero))) 1ℝ damping (0≤→isNonnegative damping damping-nonnegative)
          (≤ℝ-trans (cosℝ (sequence (suc zero))) (absℝ (cosℝ (sequence (suc zero)))) 1ℝ
            (leAbs (cosℝ (sequence (suc zero)))) (cosℝ-abs≤one (sequence (suc zero))))))
      damping≤contraction

  opaque
    initialDifference : successiveIncrements sequence zero ≡ damping
    initialDifference = cong₂ _-_ first start ∙ subZero damping

    initialAbs : absℝ (successiveIncrements sequence zero) ≡ damping
    initialAbs = cong absℝ initialDifference ∙ absOfNonnegative damping damping-nonnegative

  opaque
    incrementGeometric : ∀ n →
      absℝ (successiveIncrements sequence n) ≤ℝ 1ℝ · powℝ contraction n
    incrementGeometric zero = subst2
      {x = damping} {y = absℝ (successiveIncrements sequence zero)}
      {z = 1ℝ} {w = 1ℝ · powℝ contraction zero} _≤ℝ_
      (sym initialAbs)
      (sym (mulIdL 1ℝ)) damping≤one
    incrementGeometric (suc n) = subst2
      {x = damping · cosℝ (sequence (suc n))}
      {y = absℝ (successiveIncrements sequence (suc n))}
      {z = powℝ contraction (suc n)} {w = 1ℝ · powℝ contraction (suc n)} _≤ℝ_
      (sym (absIncrement (suc n))) (sym (mulIdL (powℝ contraction (suc n))))
      (≤ℝ-trans (damping · cosℝ (sequence (suc n)))
        ((damping · cosℝ (sequence (suc zero))) · powℝ contraction n) (contraction · powℝ contraction n)
        (subst
          {x = damping · (cosℝ (sequence (suc zero)) · powℝ contraction n)}
          {y = (damping · cosℝ (sequence (suc zero))) · powℝ contraction n}
          (damping · cosℝ (sequence (suc n)) ≤ℝ_)
          (mulAssoc damping (cosℝ (sequence (suc zero))) (powℝ contraction n))
          (mulPres≤L (cosℝ (sequence (suc n))) (cosℝ (sequence (suc zero)) · powℝ contraction n) damping
            (0≤→isNonnegative damping damping-nonnegative) (cosineGeometric n)))
        (mulPres≤R-0≤ (damping · cosℝ (sequence (suc zero))) contraction (powℝ contraction n)
          (powNonnegative contraction n contraction-nonnegative) leadingBound))

  opaque
    cauchy : SeqWitness sequence
    cauchy = geometricallyBoundedIncrementsCauchy
      sequence contraction 1ℝ contraction-nonnegative contraction<one incrementGeometric


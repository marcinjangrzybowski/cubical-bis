module Cubical.Analysis.Real.Series.PowerSeries.Logarithm.OpenDomain where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base using (ℚ; fromNatℚ; fromNat)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; min₊; min₊≤L; min₊≤R)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_; return)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Density
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Domain.OpenRadius
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Continuity
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Value
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Derivative


negativeLogOneMinusOnOpenUnit : OpenAbsRadius 1ℝ → ℝ
negativeLogOneMinusOnOpenUnit point =
  negativeLogOneMinus (fst point) (snd point)


negativeLogOneMinusReciprocalOnOpenUnit : OpenAbsRadius 1ℝ → ℝ
negativeLogOneMinusReciprocalOnOpenUnit point =
  positiveReciprocal (1ℝ - fst point)
    (positiveSub (fst point) 1ℝ
      (≤<ℝ-trans (fst point) (absℝ (fst point)) 1ℝ
        (leAbs (fst point)) (snd point)))


private
  openValueAgrees : ∀ (radius : ℚ₊) (radius<1 : fst radius ℚ.< 1)
    (point : OpenAbsRadius 1ℝ) (bounded : absℝ (fst point) ≤ℝ rat (fst radius)) →
    negativeLogOneMinusOnOpenUnit point ≡
    negativeLogOneMinusOnClosedRadius radius radius<1 (fst point , bounded)
  openValueAgrees radius radius<1 point bounded =
    negativeLogOneMinusOnClosedRadius-agrees
      radius radius<1 (fst point , bounded) (snd point)

  openReciprocalAgrees : ∀ (radius : ℚ₊) (radius<1 : fst radius ℚ.< 1)
    (point : OpenAbsRadius 1ℝ) (bounded : absℝ (fst point) ≤ℝ rat (fst radius)) →
    negativeLogOneMinusReciprocalOnOpenUnit point ≡
    negativeLogOneMinusReciprocalOnClosedRadius radius radius<1
      (fst point , bounded)
  openReciprocalAgrees radius radius<1 point bounded =
    cong (positiveReciprocal (1ℝ - fst point))
      (isProp<ℝ 0ℝ (1ℝ - fst point) _ _)


-- Each derivative estimate is localized independently to a rational closed
-- radius.  No function selecting radii on the whole open interval is chosen.
opaque
  negativeLogOneMinusHasReciprocalDerivativeOnOpenUnit :
    IsDerivativeAlong (OpenAbsRadiusPremetricSpace 1ℝ .snd) fst
      negativeLogOneMinusOnOpenUnit negativeLogOneMinusReciprocalOnOpenUnit
  negativeLogOneMinusHasReciprocalDerivativeOnOpenUnit point ε =
    PT.rec squash₁ atRadius (denseℚinℝ (absℝ (fst point)) 1ℝ (snd point))
    where
    atRadius :
      (Σ[ r ∈ ℚ ] (absℝ (fst point) <ℝ rat r) × (rat r <ℝ 1ℝ)) →
      ∃[ δ ∈ ℚ₊ ]
        (∀ other → fst point ∼[ δ ] fst other →
          absℝ (derivativeErrorAlong fst negativeLogOneMinusOnOpenUnit
            negativeLogOneMinusReciprocalOnOpenUnit point other) ≤ℝ
          rat (fst ε) · absℝ (fst other - fst point))
    atRadius (r , inside , r<1) = do
      (domain-radius , stays) ← openAbsRadiusIsOpen (rat r) (fst point) inside
      (derivative-radius , local-bound) ←
        negativeLogOneMinusHasReciprocalDerivativeOnClosedRadius
          radius radius<1 (fst point , centre-bound) ε
      return
        (min₊ derivative-radius domain-radius
        , λ other close →
            let
              near : fst point ∼[ derivative-radius ] fst other
              near = PremetricStr.isMonotone≈≤ (ℝPremetricSpace .snd)
                (fst point) (fst other) (min₊ derivative-radius domain-radius)
                derivative-radius (min₊≤L derivative-radius domain-radius) close

              domain-near : fst point ∼[ domain-radius ] fst other
              domain-near = PremetricStr.isMonotone≈≤ (ℝPremetricSpace .snd)
                (fst point) (fst other) (min₊ derivative-radius domain-radius)
                domain-radius (min₊≤R derivative-radius domain-radius) close

              bounded : absℝ (fst other) ≤ℝ rat r
              bounded = <ℝ-weaken (absℝ (fst other)) (rat r)
                (stays (fst other) domain-near)

              error-path :
                derivativeErrorAlong fst negativeLogOneMinusOnOpenUnit
                  negativeLogOneMinusReciprocalOnOpenUnit point other ≡
                derivativeErrorAlong fst
                  (negativeLogOneMinusOnClosedRadius radius radius<1)
                  (negativeLogOneMinusReciprocalOnClosedRadius radius radius<1)
                  (fst point , centre-bound) (fst other , bounded)
              error-path =
                cong₃ (λ y-value x-value derivative →
                  (y-value - x-value) - derivative · (fst other - fst point))
                  (openValueAgrees radius radius<1 other bounded)
                  (openValueAgrees radius radius<1 point centre-bound)
                  (openReciprocalAgrees radius radius<1 point centre-bound)
            in
            subst (λ error → absℝ error ≤ℝ
              rat (fst ε) · absℝ (fst other - fst point))
              (sym error-path) (local-bound (fst other , bounded) near))
      where
      radius : ℚ₊
      radius = r , <ℝ→<ℚ 0 r
        (≤<ℝ-trans 0ℝ (absℝ (fst point)) (rat r)
          (absNonnegative (fst point)) inside)

      radius<1 : fst radius ℚ.< 1
      radius<1 = <ℝ→<ℚ r 1 r<1

      centre-bound : absℝ (fst point) ≤ℝ rat r
      centre-bound = <ℝ-weaken (absℝ (fst point)) (rat r) inside

  negativeLogOneMinusOnOpenUnitIsContinuous :
    isContinuous (OpenAbsRadiusPremetricSpace 1ℝ .snd)
      negativeLogOneMinusOnOpenUnit (ℝPremetricSpace .snd)
  negativeLogOneMinusOnOpenUnitIsContinuous =
    derivativeAlongIsContinuous (OpenAbsRadiusPremetricSpace 1ℝ .snd) fst
      negativeLogOneMinusOnOpenUnit negativeLogOneMinusReciprocalOnOpenUnit
      (snd (openAbsRadiusInclusionC 1ℝ))
      negativeLogOneMinusHasReciprocalDerivativeOnOpenUnit

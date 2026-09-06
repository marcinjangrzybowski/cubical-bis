module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse using (_₊／₊_; ·／)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Continuity
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Continuity.Bounds public

open PositiveRationals using (ℚ₊)


private
  derivative-uniform :
    EntireFormalDerivativePowerSeriesUniformlyCauchy exponentialCoefficients
  derivative-uniform radius =
    exponentialPowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      radius (suc zero)

  local-derivative : ℝ → ℝ
  local-derivative x =
    entireFormalDerivativeValueAtRadius exponentialCoefficients derivative-uniform
      (entireRadiusAt x) x (entireRadiusAt-interior x)

  local-derivative-correct : IsDerivative exponentialEntireValue local-derivative
  local-derivative-correct x =
    entirePowerSeriesValueHasFormalDerivativeAtRadius
      exponentialCoefficients exponentialPowerSeriesEntireUniformlyCauchy
      derivative-uniform exponentialPowerSeriesDifferenceFactorEntireUniformlyCauchy
      (entireRadiusAt x) x (entireRadiusAt-interior x)


exponentialEntireValueIsContinuous :
  isContinuous (ℝPremetricSpace .snd) exponentialEntireValue (ℝPremetricSpace .snd)
exponentialEntireValueIsContinuous =
  derivativeIsContinuous exponentialEntireValue local-derivative local-derivative-correct


private
  intervalRadius : ℝ → ℝ → ℝ
  intervalRadius a b = absℝ a + absℝ b

  absLeft≤radius : ∀ a b → absℝ a ≤ℝ intervalRadius a b
  absLeft≤radius a b =
    subst (_≤ℝ intervalRadius a b) (addIdR (absℝ a))
      (addPres≤L 0ℝ (absℝ b) (absℝ a) (absNonnegative b))

  absRight≤radius : ∀ a b → absℝ b ≤ℝ intervalRadius a b
  absRight≤radius a b =
    subst (_≤ℝ intervalRadius a b) (addIdL (absℝ b))
      (addPres≤R 0ℝ (absℝ a) (absℝ b) (absNonnegative a))

  radiusNonnegative : ∀ a b → 0ℝ ≤ℝ intervalRadius a b
  radiusNonnegative a b =
    ≤ℝ-trans 0ℝ (absℝ a) (intervalRadius a b)
      (absNonnegative a) (absLeft≤radius a b)

  pointAbsBound : ∀ a b (point : ClosedInterval a b) →
    absℝ (fst point) ≤ℝ intervalRadius a b
  pointAbsBound a b (x , lower , upper) =
    absLeastUpperBound x (intervalRadius a b)
      (≤ℝ-trans x b (intervalRadius a b) upper
        (≤ℝ-trans b (absℝ b) (intervalRadius a b)
          (leAbs b) (absRight≤radius a b)))
      (≤ℝ-trans (- x) (- a) (intervalRadius a b)
        (negPres≤ a x lower)
        (≤ℝ-trans (- a) (absℝ a) (intervalRadius a b)
          (negLeAbs a) (absLeft≤radius a b)))

  opaque
    intervalPreservesClosenessAtBound : ∀ a b (bound : ℚ₊) →
      exponentialEntireValue (intervalRadius a b) ≤ℝ rat (fst bound) →
      ∀ (x y : ClosedInterval a b) ε →
      fst x ∼[ ε ₊／₊ bound ] fst y →
      exponentialEntireValue (fst x) ∼[ ε ] exponentialEntireValue (fst y)
    intervalPreservesClosenessAtBound a b bound exp≤bound x y ε near =
      absDifference<→closeness
        (exponentialEntireValue (fst x)) (exponentialEntireValue (fst y)) ε
        (≤<ℝ-trans
          (absℝ (exponentialEntireValue (fst x) - exponentialEntireValue (fst y)))
          (absℝ (fst x - fst y) · rat (fst bound)) (rat (fst ε))
          (≤ℝ-trans
            (absℝ (exponentialEntireValue (fst x) - exponentialEntireValue (fst y)))
            (absℝ (fst x - fst y) · exponentialEntireValue (intervalRadius a b))
            (absℝ (fst x - fst y) · rat (fst bound))
            (exponentialEntireValue-absoluteDifferenceBoundOnRadius
              (fst y) (fst x) (intervalRadius a b) (radiusNonnegative a b)
              (pointAbsBound a b y) (pointAbsBound a b x))
            (mulPres≤L
              (exponentialEntireValue (intervalRadius a b)) (rat (fst bound))
              (absℝ (fst x - fst y))
              (0≤→isNonnegative (absℝ (fst x - fst y))
                (absNonnegative (fst x - fst y))) exp≤bound))
          (subst ((absℝ (fst x - fst y) · rat (fst bound)) <ℝ_)
            (mulComm (rat (fst (ε ₊／₊ bound))) (rat (fst bound))
            ∙ mul-rat (fst bound) (fst (ε ₊／₊ bound))
            ∙ cong rat (·／ bound ε))
            (mulPres<PosR (absℝ (fst x - fst y))
              (rat (fst (ε ₊／₊ bound))) (rat (fst bound))
              (<ℚ→<ℝ 0 (fst bound) (snd bound))
              (closeness→absDifference< (fst x) (fst y) (ε ₊／₊ bound) near))))


-- One merely existing rational upper bound supplies a whole explicit modulus
-- ε ↦ ε / bound.  No countable choice is needed to package uniform continuity.
exponentialEntireValueIsUniformlyContinuousOnInterval : ∀ a b →
  isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
    (λ point → exponentialEntireValue (fst point)) (ℝPremetricSpace .snd)
exponentialEntireValueIsUniformlyContinuousOnInterval a b =
  PT.map (λ { (n , bounded) →
    (λ ε → ε ₊／₊ naturalBound n)
    , isuniformlycontinuouswith
        (intervalPreservesClosenessAtBound a b (naturalBound n)
          (<ℝ-weaken (exponentialEntireValue (intervalRadius a b))
            (rat (naturalRational n)) bounded)) })
    (∃naturalUpperBound (exponentialEntireValue (intervalRadius a b)))

exponentialEntireValueUniformContinuityOnInterval : ∀ a b ε →
  ∃[ δ ∈ ℚ₊ ]
    (∀ (x y : ClosedInterval a b) → fst x ∼[ δ ] fst y →
      exponentialEntireValue (fst x) ∼[ ε ] exponentialEntireValue (fst y))
exponentialEntireValueUniformContinuityOnInterval a b ε =
  PT.map (λ { (modulus , uniform) →
    modulus ε , λ x y → uniform .IsUniformlyContinuousWith.pres≈ x y ε })
    (exponentialEntireValueIsUniformlyContinuousOnInterval a b)

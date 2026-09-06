module Cubical.Analysis.Real.Functions.Logarithm.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse using (_₊／₊_; ·／)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties using (negSub)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Metric
open import Cubical.Analysis.Real.Domain.OpenInterval
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Functions.Exponential.Derivative
open import Cubical.Analysis.Real.Functions.Logarithm.Base
open import Cubical.Analysis.Real.Functions.Logarithm.Continuity
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Continuity.Reflection

open PositiveRationals using (ℚ₊; 1₊; min₊; min₊≤L; min₊≤R)


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)
  module Pℝ = PremetricStr (ℝPremetricSpace .snd)

  opaque
    positiveRationalNonnegative : (q : ℚ₊) → 0ℝ ≤ℝ rat (fst q)
    positiveRationalNonnegative q =
      <ℝ-weaken 0ℝ (rat (fst q)) (<ℚ→<ℝ 0 (fst q) (snd q))

    inverseErrorPath : ∀ displacement image-displacement derivative inverse →
      inverse · derivative ≡ 1ℝ →
      displacement - inverse · image-displacement ≡
      - (inverse · (image-displacement - derivative · displacement))
    inverseErrorPath displacement image-displacement derivative inverse cancel =
      sym
        (cong -_
          (ℝRing.·DistR- inverse image-displacement (derivative · displacement)
          ∙ cong (λ term → inverse · image-displacement - term)
              (mulAssoc inverse derivative displacement
              ∙ cong (_· displacement) cancel ∙ mulIdL displacement))
        ∙ negSub (inverse · image-displacement) displacement)

    rearrangeFactors : ∀ inverse tolerance factor distance →
      inverse · (tolerance · (factor · distance)) ≡
      ((inverse · factor) · tolerance) · distance
    rearrangeFactors inverse tolerance factor distance =
      cong (inverse ·_) (mulAssoc tolerance factor distance)
      ∙ mulAssoc inverse (tolerance · factor) distance
      ∙ cong (_· distance)
          (cong (inverse ·_) (mulComm tolerance factor)
          ∙ mulAssoc inverse factor tolerance)

    inverseRemainderEstimate : ∀ displacement image-displacement derivative inverse factor →
      (ε bound : ℚ₊) →
      inverse · derivative ≡ 1ℝ →
      absℝ (image-displacement - derivative · displacement) ≤ℝ
        rat (fst (ε ₊／₊ bound)) · absℝ displacement →
      absℝ displacement ≤ℝ factor · absℝ image-displacement →
      absℝ inverse · factor ≤ℝ rat (fst bound) →
      absℝ (displacement - inverse · image-displacement) ≤ℝ
        rat (fst ε) · absℝ image-displacement
    inverseRemainderEstimate displacement image-displacement derivative inverse factor
        ε bound cancel remainder-bound inverse-bound coefficient-bound =
      subst (_≤ℝ rat (fst ε) · absℝ image-displacement)
        (sym absolute-error)
        (≤ℝ-trans (absℝ inverse · absℝ remainder)
          (absℝ inverse · (tolerance · absℝ displacement))
          (rat (fst ε) · absℝ image-displacement)
          (mulPres≤L (absℝ remainder) (tolerance · absℝ displacement)
            (absℝ inverse) inverse-nonnegative remainder-bound)
          (≤ℝ-trans (absℝ inverse · (tolerance · absℝ displacement))
            (absℝ inverse · (tolerance · (factor · absℝ image-displacement)))
            (rat (fst ε) · absℝ image-displacement)
            (mulPres≤L (tolerance · absℝ displacement)
              (tolerance · (factor · absℝ image-displacement))
              (absℝ inverse) inverse-nonnegative
              (mulPres≤L (absℝ displacement) (factor · absℝ image-displacement)
                tolerance tolerance-nonnegative inverse-bound))
            (subst (_≤ℝ rat (fst ε) · absℝ image-displacement)
              (sym (rearrangeFactors (absℝ inverse) tolerance factor
                (absℝ image-displacement)))
              (subst
                (((absℝ inverse · factor) · tolerance) · absℝ image-displacement ≤ℝ_)
                (cong (_· absℝ image-displacement)
                  (mul-rat (fst bound) (fst (ε ₊／₊ bound))
                  ∙ cong rat (·／ bound ε)))
                (mulPres≤R-0≤ ((absℝ inverse · factor) · tolerance)
                  (rat (fst bound) · tolerance) (absℝ image-displacement)
                  (absNonnegative image-displacement)
                  (mulPres≤R-0≤ (absℝ inverse · factor) (rat (fst bound)) tolerance
                    (positiveRationalNonnegative (ε ₊／₊ bound)) coefficient-bound))))))
      where
      remainder : ℝ
      remainder = image-displacement - derivative · displacement

      tolerance : ℝ
      tolerance = rat (fst (ε ₊／₊ bound))

      inverse-nonnegative : IsNonnegative (absℝ inverse)
      inverse-nonnegative =
        0≤→isNonnegative (absℝ inverse) (absNonnegative inverse)

      tolerance-nonnegative : IsNonnegative tolerance
      tolerance-nonnegative =
        0≤→isNonnegative tolerance (positiveRationalNonnegative (ε ₊／₊ bound))

      absolute-error : absℝ (displacement - inverse · image-displacement) ≡
        absℝ inverse · absℝ remainder
      absolute-error =
        cong absℝ (inverseErrorPath displacement image-displacement derivative inverse cancel)
        ∙ absNeg (inverse · remainder) ∙ absMul inverse remainder


-- The derivative is the existing positive-real reciprocal, not a quotient
-- newly chosen from the equivalence witness.
logarithmDerivative : ℝ>0 → ℝ
logarithmDerivative point = positiveReciprocal (fst point) (snd point)

logarithmHasDerivative : (equivalent : isEquiv expPositive) →
  IsDerivativeAlong (LowerOpenHalfLinePremetricSpace 0ℝ .snd) fst
    (logarithmFromEquivalence equivalent) logarithmDerivative
logarithmHasDerivative equivalent point ε =
  PT.rec squash₁ (λ { (n , bounded) →
    atBound (naturalBound n)
      (<ℝ-weaken (absℝ inverse · factor) (rat (naturalRational n)) bounded) })
    (∃naturalUpperBound (absℝ inverse · factor))
  where
  inverse : ℝ
  inverse = logarithmDerivative point

  source-floor : ℝ
  source-floor = logarithmFromEquivalence equivalent point - 1ℝ

  factor : ℝ
  factor = exponentialEntireValue (- source-floor)

  point-above : source-floor ≤ℝ logarithmFromEquivalence equivalent point
  point-above = close→lowerBound (logarithmFromEquivalence equivalent point) (logarithmFromEquivalence equivalent point) 1₊
    (refl∼ (logarithmFromEquivalence equivalent point) 1₊)

  atBound : (bound : ℚ₊) → absℝ inverse · factor ≤ℝ rat (fst bound) →
    ∃[ δ ∈ ℚ₊ ] (∀ value → fst point ∼[ δ ] fst value →
      absℝ ((logarithmFromEquivalence equivalent value - logarithmFromEquivalence equivalent point) - inverse · (fst value - fst point)) ≤ℝ
      rat (fst ε) · absℝ (fst value - fst point))
  atBound bound coefficient-bound =
    PT.rec squash₁ atExponentialRadius
      (exponentialHasSelfDerivative (logarithmFromEquivalence equivalent point) (ε ₊／₊ bound))
    where
    atExponentialRadius :
      (Σ[ radius ∈ ℚ₊ ] (∀ y → logarithmFromEquivalence equivalent point ∼[ radius ] y →
        absℝ ((expℝ y - expℝ (logarithmFromEquivalence equivalent point)) -
          expℝ (logarithmFromEquivalence equivalent point) · (y - logarithmFromEquivalence equivalent point)) ≤ℝ
        rat (fst (ε ₊／₊ bound)) · absℝ (y - logarithmFromEquivalence equivalent point))) →
      ∃[ δ ∈ ℚ₊ ] (∀ value → fst point ∼[ δ ] fst value →
        absℝ ((logarithmFromEquivalence equivalent value - logarithmFromEquivalence equivalent point) - inverse · (fst value - fst point)) ≤ℝ
        rat (fst ε) · absℝ (fst value - fst point))
    atExponentialRadius (radius , remainder-bound) =
      PT.map (λ { (δ , preserves) →
        δ , λ value near → estimate value (preserves value near) })
        (logarithmFromEquivalenceIsContinuous equivalent point .IsContinuousAt.pres≈
          (min₊ radius 1₊))
      where
      estimate : ∀ value → logarithmFromEquivalence equivalent point ∼[ min₊ radius 1₊ ] logarithmFromEquivalence equivalent value →
        absℝ ((logarithmFromEquivalence equivalent value - logarithmFromEquivalence equivalent point) - inverse · (fst value - fst point)) ≤ℝ
        rat (fst ε) · absℝ (fst value - fst point)
      estimate value log-close =
        inverseRemainderEstimate
          (logarithmFromEquivalence equivalent value - logarithmFromEquivalence equivalent point) (fst value - fst point)
          (fst point) inverse factor ε bound
          (positiveReciprocalLaw' (fst point) (snd point))
          exponential-error inverse-distance coefficient-bound
        where
        value-above : source-floor ≤ℝ logarithmFromEquivalence equivalent value
        value-above =
          close→lowerBound (logarithmFromEquivalence equivalent value) (logarithmFromEquivalence equivalent point) 1₊
            (sym∼ (logarithmFromEquivalence equivalent point) (logarithmFromEquivalence equivalent value) 1₊
              (Pℝ.isMonotone≈≤ (logarithmFromEquivalence equivalent point) (logarithmFromEquivalence equivalent value)
                (min₊ radius 1₊) 1₊ (min₊≤R radius 1₊) log-close))

        exponential-error :
          absℝ ((fst value - fst point) - fst point · (logarithmFromEquivalence equivalent value - logarithmFromEquivalence equivalent point)) ≤ℝ
          rat (fst (ε ₊／₊ bound)) · absℝ (logarithmFromEquivalence equivalent value - logarithmFromEquivalence equivalent point)
        exponential-error =
          subst2 (λ image-value image-point →
            absℝ ((image-value - image-point) -
              image-point · (logarithmFromEquivalence equivalent value - logarithmFromEquivalence equivalent point)) ≤ℝ
            rat (fst (ε ₊／₊ bound)) · absℝ (logarithmFromEquivalence equivalent value - logarithmFromEquivalence equivalent point))
            (expℝ-logarithm equivalent value) (expℝ-logarithm equivalent point)
            (remainder-bound (logarithmFromEquivalence equivalent value)
              (Pℝ.isMonotone≈≤ (logarithmFromEquivalence equivalent point) (logarithmFromEquivalence equivalent value)
                (min₊ radius 1₊) radius (min₊≤L radius 1₊) log-close))

        inverse-distance : absℝ (logarithmFromEquivalence equivalent value - logarithmFromEquivalence equivalent point) ≤ℝ
          factor · absℝ (fst value - fst point)
        inverse-distance =
          subst (absℝ (logarithmFromEquivalence equivalent value - logarithmFromEquivalence equivalent point) ≤ℝ_)
            (cong (λ distance → factor · absℝ distance)
              (cong₂ _-_ (expℝ-logarithm equivalent value) (expℝ-logarithm equivalent point)))
            (exponentialEntireValue-inverseDifferenceBound
              source-floor (logarithmFromEquivalence equivalent value) (logarithmFromEquivalence equivalent point) value-above point-above)

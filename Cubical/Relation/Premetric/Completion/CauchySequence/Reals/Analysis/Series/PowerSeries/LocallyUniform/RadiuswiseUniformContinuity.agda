module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.RadiuswiseUniformContinuity where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals.Base
import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
  using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
  using (≤ℝ-trans)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
  using (≤ℚ→≤ℝ)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Clamp
  using
    ( absBound→symmetricIntervalBounds
    ; symmetricIntervalBounds→absBound
    )
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (JointRationalBound ; ∃jointRationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Interval
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity.UniformLimit


closedPositiveRationalRadiusCoordinateIsRadiuswiseUniformlyContinuous :
  (radius : ℚ₊) →
  IsRadiuswiseUniformlyContinuous
    (snd (ClosedAbsRadiusPremetricSpace
      (Real.ιℚ (fst radius))))
    fst
    (snd Real.ℝPremetricSpace)
closedPositiveRationalRadiusCoordinateIsRadiuswiseUniformlyContinuous
  radius ε =
  ∣ ε , (λ _ _ point≈other → point≈other) ∣₁


closedPositiveRationalRadiusPowerBound :
  (radius : ℚ₊) →
  (point : ClosedAbsRadius (Real.ιℚ (fst radius))) →
  (n : ℕ) →
  Abs.absℝ (fst point ^ⁿ n) ≤ℝ
    Real.ιℚ (fst (radius ^₊ n))
closedPositiveRationalRadiusPowerBound radius point n =
  subst2 _≤ℝ_
    (sym (absPow n (fst point)))
    (pow-ι n (fst radius))
    (powMono n (zero≤abs (fst point)) (snd point))


closedPositiveRationalRadiusPowerIsRadiuswiseUniformlyContinuous :
  (radius : ℚ₊) → (n : ℕ) →
  IsRadiuswiseUniformlyContinuous
    (snd (ClosedAbsRadiusPremetricSpace
      (Real.ιℚ (fst radius))))
    (λ point → fst point ^ⁿ n)
    (snd Real.ℝPremetricSpace)
closedPositiveRationalRadiusPowerIsRadiuswiseUniformlyContinuous
  radius zero =
  constantIsRadiuswiseUniformlyContinuous
    (snd (ClosedAbsRadiusPremetricSpace
      (Real.ιℚ (fst radius))))
    (Real.ιℚ 1)
closedPositiveRationalRadiusPowerIsRadiuswiseUniformlyContinuous
  radius (suc n) =
  mulOfBoundedRadiuswiseUniformlyContinuous
    source bound
    fst
    (λ point → fst point ^ⁿ n)
    coordinate-bounded power-bounded
    (closedPositiveRationalRadiusCoordinateIsRadiuswiseUniformlyContinuous
      radius)
    (closedPositiveRationalRadiusPowerIsRadiuswiseUniformlyContinuous
      radius n)
  where
  source : PremetricStr ℓ-zero (ClosedAbsRadius (Real.ιℚ (fst radius)))
  source = snd (ClosedAbsRadiusPremetricSpace
    (Real.ιℚ (fst radius)))

  bound : ℚ₊
  bound = max₊ radius (radius ^₊ n)

  coordinate-bounded : ∀ point →
    Abs.absℝ (fst point) ≤ℝ Real.ιℚ (fst bound)
  coordinate-bounded point =
    ≤ℝ-trans
      (Abs.absℝ (fst point))
      (Real.ιℚ (fst radius))
      (Real.ιℚ (fst bound))
      (snd point)
      (≤ℚ→≤ℝ
        (fst radius) (fst bound)
        (ℚ.≤max (fst radius) (fst (radius ^₊ n))))

  power-bounded : ∀ point →
    Abs.absℝ (fst point ^ⁿ n) ≤ℝ Real.ιℚ (fst bound)
  power-bounded point =
    ≤ℝ-trans
      (Abs.absℝ (fst point ^ⁿ n))
      (Real.ιℚ (fst (radius ^₊ n)))
      (Real.ιℚ (fst bound))
      (closedPositiveRationalRadiusPowerBound radius point n)
      (≤ℚ→≤ℝ
        (fst (radius ^₊ n)) (fst bound)
        (ℚ.≤max' (fst radius) (fst (radius ^₊ n))))


powerSeriesTermOnClosedPositiveRationalRadiusIsRadiuswiseUniformlyContinuous :
  (coefficients : RealSequence) → (radius : ℚ₊) → (n : ℕ) →
  IsRadiuswiseUniformlyContinuous
    (snd (ClosedAbsRadiusPremetricSpace
      (Real.ιℚ (fst radius))))
    (λ point →
      powerSeriesTermsOnClosedRadius
        coefficients (Real.ιℚ (fst radius)) point n)
    (snd Real.ℝPremetricSpace)
powerSeriesTermOnClosedPositiveRationalRadiusIsRadiuswiseUniformlyContinuous
  coefficients radius n =
  scaleIsRadiuswiseUniformlyContinuous
    (snd (ClosedAbsRadiusPremetricSpace
      (Real.ιℚ (fst radius))))
    (coefficients n)
    (λ point → fst point ^ⁿ n)
    (closedPositiveRationalRadiusPowerIsRadiuswiseUniformlyContinuous
      radius n)


powerSeriesUniformValueOnClosedPositiveRationalRadiusIsRadiuswiseUniformlyContinuous :
  (coefficients : RealSequence) → (radius : ℚ₊) →
    (uniform : PowerSeriesUniformlyCauchyOnRadius
      coefficients (Real.ιℚ (fst radius))) →
  IsRadiuswiseUniformlyContinuous
    (snd (ClosedAbsRadiusPremetricSpace
      (Real.ιℚ (fst radius))))
    (powerSeriesUniformValueOnClosedRadius
      coefficients (Real.ιℚ (fst radius)) uniform)
    (snd Real.ℝPremetricSpace)
powerSeriesUniformValueOnClosedPositiveRationalRadiusIsRadiuswiseUniformlyContinuous
  coefficients radius uniform =
  uniformSeriesValueIsRadiuswiseUniformlyContinuous
    (snd (ClosedAbsRadiusPremetricSpace
      (Real.ιℚ (fst radius))))
    (powerSeriesTermsOnClosedRadius
      coefficients (Real.ιℚ (fst radius)))
    uniform
    (powerSeriesTermOnClosedPositiveRationalRadiusIsRadiuswiseUniformlyContinuous
      coefficients radius)


-- The canonical whole-line evaluator inherits the same radiuswise uniform
-- continuity after restriction to every rational closed ball.  Agreement is
-- used opaquely, so no Archimedean radius witness is unfolded here.

locallyUniformPowerSeriesValueOnClosedRadiusIsRadiuswiseUniformlyContinuous :
  ∀ (coefficients : RealSequence)
    (local : LocallyUniformPowerSeries coefficients)
    (radius : ℚ₊) →
  IsRadiuswiseUniformlyContinuous
    (snd (ClosedAbsRadiusPremetricSpace
      (Real.ιℚ (fst radius))))
    (λ point →
      locallyUniformPowerSeriesValue coefficients local (fst point))
    (snd Real.ℝPremetricSpace)
locallyUniformPowerSeriesValueOnClosedRadiusIsRadiuswiseUniformlyContinuous
  coefficients local radius =
  radiuswiseUniformlyContinuous-cong
    (snd (ClosedAbsRadiusPremetricSpace
      (Real.ιℚ (fst radius))))
    (powerSeriesUniformValueOnClosedRadius
      coefficients (Real.ιℚ (fst radius)) (local radius))
    (λ point →
      locallyUniformPowerSeriesValue coefficients local (fst point))
    (λ point → sym
      (locallyUniformPowerSeriesValue-agreesOnRadius
        coefficients local radius point))
    (powerSeriesUniformValueOnClosedPositiveRationalRadiusIsRadiuswiseUniformlyContinuous
      coefficients radius (local radius))


-- Every real closed interval sits in a merely existing positive rational
-- ball.  Since radiuswise uniform continuity is a proposition, that one
-- finite bound can be opened and discarded.  The resulting theorem exposes
-- no radius choice and is the interface needed by Riemann integration.

locallyUniformPowerSeriesValueOnClosedIntervalIsRadiuswiseUniformlyContinuous :
  ∀ (coefficients : RealSequence)
    (local : LocallyUniformPowerSeries coefficients)
    a b →
  IsRadiuswiseUniformlyContinuous
    (snd (ClosedIntervalPremetricSpace a b))
    (λ point →
      locallyUniformPowerSeriesValue coefficients local (fst point))
    (snd Real.ℝPremetricSpace)
locallyUniformPowerSeriesValueOnClosedIntervalIsRadiuswiseUniformlyContinuous
  coefficients local a b =
  PT.rec
    (isPropIsRadiuswiseUniformlyContinuous
      (snd (ClosedIntervalPremetricSpace a b))
      (λ point →
        locallyUniformPowerSeriesValue coefficients local (fst point))
      (snd Real.ℝPremetricSpace))
    bounded-interval
    (∃jointRationalBound a b)
  where
  bounded-interval : JointRationalBound a b →
    IsRadiuswiseUniformlyContinuous
      (snd (ClosedIntervalPremetricSpace a b))
      (λ point →
        locallyUniformPowerSeriesValue coefficients local (fst point))
      (snd Real.ℝPremetricSpace)
  bounded-interval (radius , absa≤radius , absb≤radius) =
    radiuswisePrecomposeNonExpanding
      (snd (ClosedIntervalPremetricSpace a b))
      (snd (ClosedAbsRadiusPremetricSpace
        (Real.ιℚ (fst radius))))
      (snd Real.ℝPremetricSpace)
      interval-to-radius
      (λ point →
        locallyUniformPowerSeriesValue coefficients local (fst point))
      interval-to-radius-ne
      (locallyUniformPowerSeriesValueOnClosedRadiusIsRadiuswiseUniformlyContinuous
        coefficients local radius)
    where
    interval-to-radius :
      ClosedInterval a b →
      ClosedAbsRadius (Real.ιℚ (fst radius))
    interval-to-radius point = fst point ,
      symmetricIntervalBounds→absBound
        (Real.ιℚ (fst radius)) (fst point)
        (≤ℝ-trans
          (Neg.- Real.ιℚ (fst radius)) a (fst point)
          (fst (absBound→symmetricIntervalBounds
            (Real.ιℚ (fst radius)) a absa≤radius))
          (fst (snd point)))
        (≤ℝ-trans
          (fst point) b (Real.ιℚ (fst radius))
          (snd (snd point))
          (snd (absBound→symmetricIntervalBounds
            (Real.ιℚ (fst radius)) b absb≤radius)))

    interval-to-radius-ne :
      IsNonExpanding
        (snd (ClosedIntervalPremetricSpace a b))
        interval-to-radius
        (snd (ClosedAbsRadiusPremetricSpace
          (Real.ιℚ (fst radius))))
    interval-to-radius-ne .IsNonExpanding.pres≈
      point other ε point≈other = point≈other

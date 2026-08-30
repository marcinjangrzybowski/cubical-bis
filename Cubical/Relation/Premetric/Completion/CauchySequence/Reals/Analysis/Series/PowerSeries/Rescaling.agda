module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Rescaling where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base
import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using
    ( abs-mul
    ; mul-preserves≤-left-nonnegative
    ; mul-monotone-nonnegative
    )
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (RationalBound ; ∃rationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform.Reindex
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform


-- Algebraic substitution x ↦ c·x is represented coefficientwise.  This
-- keeps the operation available before any convergence hypothesis is chosen.

rescaleCoefficients : Real.ℝ → RealSequence → RealSequence
rescaleCoefficients c coefficients n =
  coefficients n Mul.· c ^ⁿ n


rescaleCoefficients-one : ∀ coefficients →
  rescaleCoefficients (Real.ιℚ 1) coefficients ≡ coefficients
rescaleCoefficients-one coefficients =
  funExt λ n →
      cong ((coefficients n) Mul.·_) (onePow n)
    ∙ mul-one-right (coefficients n)


rescaleCoefficients-compose : ∀ c d coefficients →
  rescaleCoefficients c (rescaleCoefficients d coefficients)
    ≡
  rescaleCoefficients (d Mul.· c) coefficients
rescaleCoefficients-compose c d coefficients =
  funExt λ n →
      sym
        (mul-assoc
          (coefficients n) (d ^ⁿ n) (c ^ⁿ n))
    ∙ cong
        ((coefficients n) Mul.·_)
        (sym (ℝExponentiation.^-ldist-· d c n))


powerSeriesTerms-rescale : ∀ c coefficients x n →
  powerSeriesTerms (rescaleCoefficients c coefficients) x n
    ≡
  powerSeriesTerms coefficients (c Mul.· x) n
powerSeriesTerms-rescale c coefficients x n =
    sym
      (mul-assoc
        (coefficients n) (c ^ⁿ n) (x ^ⁿ n))
  ∙ cong
      ((coefficients n) Mul.·_)
      (sym (ℝExponentiation.^-ldist-· c x n))


powerSeriesTerms-rescale-sequence : ∀ c coefficients x →
  powerSeriesTerms (rescaleCoefficients c coefficients) x
    ≡
  powerSeriesTerms coefficients (c Mul.· x)
powerSeriesTerms-rescale-sequence c coefficients x =
  funExt (powerSeriesTerms-rescale c coefficients x)


rescalePowerSeriesSummable : ∀ c coefficients x →
  PowerSeriesSummableAt coefficients (c Mul.· x) →
  PowerSeriesSummableAt (rescaleCoefficients c coefficients) x
rescalePowerSeriesSummable c coefficients x summable =
  subst Summable
    (sym (powerSeriesTerms-rescale-sequence c coefficients x))
    summable


rescalePowerSeriesReflectsSummable : ∀ c coefficients x →
  PowerSeriesSummableAt (rescaleCoefficients c coefficients) x →
  PowerSeriesSummableAt coefficients (c Mul.· x)
rescalePowerSeriesReflectsSummable c coefficients x summable =
  subst Summable
    (powerSeriesTerms-rescale-sequence c coefficients x)
    summable


rescalePowerSeriesHasSum : ∀ c coefficients x value →
  HasSum (powerSeriesTerms coefficients (c Mul.· x)) value →
  HasSum
    (powerSeriesTerms (rescaleCoefficients c coefficients) x) value
rescalePowerSeriesHasSum c coefficients x value has-sum =
  subst (λ terms → HasSum terms value)
    (sym (powerSeriesTerms-rescale-sequence c coefficients x))
    has-sum


rescalePowerSeriesReflectsHasSum : ∀ c coefficients x value →
  HasSum
    (powerSeriesTerms (rescaleCoefficients c coefficients) x) value →
  HasSum (powerSeriesTerms coefficients (c Mul.· x)) value
rescalePowerSeriesReflectsHasSum c coefficients x value has-sum =
  subst (λ terms → HasSum terms value)
    (powerSeriesTerms-rescale-sequence c coefficients x)
    has-sum


powerSeriesValue-rescale : ∀ c coefficients x →
  (original-summable :
    PowerSeriesSummableAt coefficients (c Mul.· x)) →
  (rescaled-summable :
    PowerSeriesSummableAt
      (rescaleCoefficients c coefficients) x) →
  powerSeriesValue
      (rescaleCoefficients c coefficients) x rescaled-summable
    ≡
  powerSeriesValue coefficients (c Mul.· x) original-summable
powerSeriesValue-rescale
  c coefficients x original-summable rescaled-summable =
  seriesSumPresPath
    (powerSeriesTerms (rescaleCoefficients c coefficients) x)
    (powerSeriesTerms coefficients (c Mul.· x))
    (powerSeriesTerms-rescale-sequence c coefficients x)
    rescaled-summable original-summable


-- Uniform convergence transports along the bounded map x ↦ c·x.  The
-- explicit radius inequality is useful beyond rational radii (for example,
-- on an interval whose radius is itself a completed real).

rescaleClosedRadius : ∀ c inner-radius outer-radius →
  Abs.absℝ c Mul.· inner-radius ≤ℝ outer-radius →
  ClosedAbsRadius inner-radius →
  ClosedAbsRadius outer-radius
rescaleClosedRadius c inner-radius outer-radius scaled-radius≤outer
  (x , absx≤inner) =
  c Mul.· x
  , subst
      (_≤ℝ outer-radius)
      (sym (abs-mul c x))
      (≤ℝ-trans
        (Abs.absℝ c Mul.· Abs.absℝ x)
        (Abs.absℝ c Mul.· inner-radius)
        outer-radius
        (mul-preserves≤-left-nonnegative
          (Abs.absℝ x) inner-radius (Abs.absℝ c)
          absx≤inner (zero≤abs c))
        scaled-radius≤outer)


rescalePowerSeriesUniformlyCauchyOnRadius :
  ∀ c coefficients inner-radius outer-radius →
  Abs.absℝ c Mul.· inner-radius ≤ℝ outer-radius →
  PowerSeriesUniformlyCauchyOnRadius coefficients outer-radius →
  PowerSeriesUniformlyCauchyOnRadius
    (rescaleCoefficients c coefficients) inner-radius
rescalePowerSeriesUniformlyCauchyOnRadius
  c coefficients inner-radius outer-radius
  scaled-radius≤outer uniform =
  uniformlyCauchySeriesPresPointwisePath
    (ClosedAbsRadius inner-radius)
    original-after-map rescaled-on-inner
    (λ point →
      sym
        (powerSeriesTerms-rescale-sequence
          c coefficients (fst point)))
    original-uniform-after-map
  where
  radius-map :
    ClosedAbsRadius inner-radius → ClosedAbsRadius outer-radius
  radius-map =
    rescaleClosedRadius
      c inner-radius outer-radius scaled-radius≤outer

  original-after-map : ClosedAbsRadius inner-radius → RealSequence
  original-after-map =
    powerSeriesTermsOnClosedRadius coefficients outer-radius ∘
      radius-map

  rescaled-on-inner : ClosedAbsRadius inner-radius → RealSequence
  rescaled-on-inner =
    powerSeriesTermsOnClosedRadius
      (rescaleCoefficients c coefficients) inner-radius

  original-uniform-after-map :
    UniformlyCauchySeries
      (ClosedAbsRadius inner-radius) original-after-map
  original-uniform-after-map =
    uniformlyCauchySeriesPrecompose
      (ClosedAbsRadius inner-radius)
      (ClosedAbsRadius outer-radius)
      (powerSeriesTermsOnClosedRadius coefficients outer-radius)
      uniform radius-map


rescalePowerSeriesUniformlyAbsolutelyCauchyOnRadius :
  ∀ c coefficients inner-radius outer-radius →
  Abs.absℝ c Mul.· inner-radius ≤ℝ outer-radius →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    coefficients outer-radius →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    (rescaleCoefficients c coefficients) inner-radius
rescalePowerSeriesUniformlyAbsolutelyCauchyOnRadius
  c coefficients inner-radius outer-radius
  scaled-radius≤outer uniform =
  uniformlyAbsolutelyCauchySeriesPresPointwisePath
    (ClosedAbsRadius inner-radius)
    original-after-map rescaled-on-inner
    (λ point →
      sym
        (powerSeriesTerms-rescale-sequence
          c coefficients (fst point)))
    original-uniform-after-map
  where
  radius-map :
    ClosedAbsRadius inner-radius → ClosedAbsRadius outer-radius
  radius-map =
    rescaleClosedRadius
      c inner-radius outer-radius scaled-radius≤outer

  original-after-map : ClosedAbsRadius inner-radius → RealSequence
  original-after-map =
    powerSeriesTermsOnClosedRadius coefficients outer-radius ∘
      radius-map

  rescaled-on-inner : ClosedAbsRadius inner-radius → RealSequence
  rescaled-on-inner =
    powerSeriesTermsOnClosedRadius
      (rescaleCoefficients c coefficients) inner-radius

  original-uniform-after-map :
    UniformlyAbsolutelyCauchySeries
      (ClosedAbsRadius inner-radius) original-after-map
  original-uniform-after-map =
    uniformlyAbsolutelyCauchySeriesPrecompose
      (ClosedAbsRadius inner-radius)
      (ClosedAbsRadius outer-radius)
      (powerSeriesTermsOnClosedRadius coefficients outer-radius)
      uniform radius-map


private
  rationalRescaleRadiusBound : ∀ c
    (bound : RationalBound c) (radius : ℚ₊) →
    Abs.absℝ c Mul.· Real.ιℚ (fst radius) ≤ℝ
    Real.ιℚ (fst (fst bound ·₊ radius))
  rationalRescaleRadiusBound c (bound-radius , absc≤bound) radius =
    subst
      ((Abs.absℝ c Mul.· Real.ιℚ (fst radius)) ≤ℝ_)
      (Mul.mul-ι-ι (fst bound-radius) (fst radius))
      (mul-monotone-nonnegative
        (Abs.absℝ c) (Real.ιℚ (fst bound-radius))
        (Real.ιℚ (fst radius)) (Real.ιℚ (fst radius))
        absc≤bound (≤ℝ-refl (Real.ιℚ (fst radius)))
        (zero≤abs c)
        (≤ℚ→≤ℝ 0 (fst radius)
          (ℚ.<Weaken≤ 0 (fst radius) (snd radius))))


-- Whole-line local uniformity is closed under arbitrary real rescaling.
-- Only one Archimedean bound for c is opened at each requested radius, and
-- the resulting common Cauchy cutoff remains propositionally truncated.

rescaleLocallyUniformPowerSeries : ∀ c coefficients →
  LocallyUniformPowerSeries coefficients →
  LocallyUniformPowerSeries (rescaleCoefficients c coefficients)
rescaleLocallyUniformPowerSeries c coefficients local radius =
  PT.rec
    (isPropUniformlyCauchySeries
      (ClosedAbsRadius (Real.ιℚ (fst radius)))
      (powerSeriesTermsOnClosedRadius
        (rescaleCoefficients c coefficients)
        (Real.ιℚ (fst radius))))
    use-bound
    (∃rationalBound c)
  where
  use-bound : RationalBound c →
    PowerSeriesUniformlyCauchyOnRadius
      (rescaleCoefficients c coefficients)
      (Real.ιℚ (fst radius))
  use-bound bound =
    rescalePowerSeriesUniformlyCauchyOnRadius
      c coefficients
      (Real.ιℚ (fst radius))
      (Real.ιℚ (fst (fst bound ·₊ radius)))
      (rationalRescaleRadiusBound c bound radius)
      (local (fst bound ·₊ radius))


locallyUniformPowerSeriesValue-rescale : ∀ c coefficients
  (local : LocallyUniformPowerSeries coefficients)
  (rescaled-local :
    LocallyUniformPowerSeries (rescaleCoefficients c coefficients))
  x →
  locallyUniformPowerSeriesValue
      (rescaleCoefficients c coefficients) rescaled-local x
    ≡
  locallyUniformPowerSeriesValue coefficients local (c Mul.· x)
locallyUniformPowerSeriesValue-rescale
  c coefficients local rescaled-local x =
  seriesSumIndependent
    (powerSeriesTerms (rescaleCoefficients c coefficients) x)
    ( locallyUniformPowerSeriesValue
        (rescaleCoefficients c coefficients) rescaled-local x
    , locallyUniformPowerSeriesValueHasSum
        (rescaleCoefficients c coefficients) rescaled-local x
    )
    ( locallyUniformPowerSeriesValue coefficients local (c Mul.· x)
    , rescalePowerSeriesHasSum c coefficients x
        (locallyUniformPowerSeriesValue coefficients local (c Mul.· x))
        (locallyUniformPowerSeriesValueHasSum
          coefficients local (c Mul.· x))
    )

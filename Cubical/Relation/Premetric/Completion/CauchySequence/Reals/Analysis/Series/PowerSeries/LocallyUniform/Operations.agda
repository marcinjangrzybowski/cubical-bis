module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Rationals.Base

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Derivative


-- The locally uniform interface is closed under the linear operations needed
-- for constructing new analytic functions.  Each radius combines only the
-- tails needed at that radius, rather than choosing a global modulus.

addLocallyUniformPowerSeries : ∀ a b →
  LocallyUniformPowerSeries a →
  LocallyUniformPowerSeries b →
  LocallyUniformPowerSeries (λ n → a n Add.+ b n)
addLocallyUniformPowerSeries a b a-local b-local radius =
  subst
    (UniformlyCauchySeries
      (ClosedAbsRadius (Real.ιℚ (fst radius))))
    (sym terms-path)
    (addUniformlyCauchySeries
      (ClosedAbsRadius (Real.ιℚ (fst radius)))
      (powerSeriesTermsOnClosedRadius
        a (Real.ιℚ (fst radius)))
      (powerSeriesTermsOnClosedRadius
        b (Real.ιℚ (fst radius)))
      (a-local radius) (b-local radius))
  where
  terms-path :
    powerSeriesTermsOnClosedRadius
      (λ n → a n Add.+ b n) (Real.ιℚ (fst radius))
      ≡
    (λ point n →
      powerSeriesTermsOnClosedRadius
        a (Real.ιℚ (fst radius)) point n
        Add.+
      powerSeriesTermsOnClosedRadius
        b (Real.ιℚ (fst radius)) point n)
  terms-path = funExt λ point →
    powerSeriesTerms-add-sequence a b (fst point)


scaleLocallyUniformPowerSeries : ∀ c coefficients →
  LocallyUniformPowerSeries coefficients →
  LocallyUniformPowerSeries (scaleSeries c coefficients)
scaleLocallyUniformPowerSeries c coefficients local radius =
  subst
    (UniformlyCauchySeries
      (ClosedAbsRadius (Real.ιℚ (fst radius))))
    (sym terms-path)
    (scaleUniformlyCauchySeries
      (ClosedAbsRadius (Real.ιℚ (fst radius))) c
      (powerSeriesTermsOnClosedRadius
        coefficients (Real.ιℚ (fst radius)))
      (local radius))
  where
  terms-path :
    powerSeriesTermsOnClosedRadius
      (scaleSeries c coefficients) (Real.ιℚ (fst radius))
      ≡
    (λ point →
      scaleSeries c
        (powerSeriesTermsOnClosedRadius
          coefficients (Real.ιℚ (fst radius)) point))
  terms-path = funExt λ point →
    powerSeriesTerms-scale-sequence c coefficients (fst point)


formalDerivativeAddLocallyUniform : ∀ a b →
  LocallyUniformPowerSeries (formalDerivative a) →
  LocallyUniformPowerSeries (formalDerivative b) →
  LocallyUniformPowerSeries
    (formalDerivative (λ n → a n Add.+ b n))
formalDerivativeAddLocallyUniform a b a-local b-local =
  subst LocallyUniformPowerSeries
    (sym (formalDerivative-add a b))
    (addLocallyUniformPowerSeries
      (formalDerivative a) (formalDerivative b)
      a-local b-local)


formalDerivativeScaleLocallyUniform : ∀ c coefficients →
  LocallyUniformPowerSeries (formalDerivative coefficients) →
  LocallyUniformPowerSeries
    (formalDerivative (scaleSeries c coefficients))
formalDerivativeScaleLocallyUniform c coefficients local =
  subst LocallyUniformPowerSeries
    (sym (formalDerivative-scale c coefficients))
    (scaleLocallyUniformPowerSeries
      c (formalDerivative coefficients) local)


addLocallyUniformPowerSeriesDifferenceFactor : ∀ a b →
  LocallyUniformPowerSeriesDifferenceFactor a →
  LocallyUniformPowerSeriesDifferenceFactor b →
  LocallyUniformPowerSeriesDifferenceFactor
    (λ n → a n Add.+ b n)
addLocallyUniformPowerSeriesDifferenceFactor
  a b a-factor b-factor radius =
  subst
    (UniformlyCauchySeries
      (ClosedAbsRadiusPair (Real.ιℚ (fst radius))))
    (sym terms-path)
    (addUniformlyCauchySeries
      (ClosedAbsRadiusPair (Real.ιℚ (fst radius)))
      (powerSeriesDifferenceFactorOnClosedRadius
        a (Real.ιℚ (fst radius)))
      (powerSeriesDifferenceFactorOnClosedRadius
        b (Real.ιℚ (fst radius)))
      (a-factor radius) (b-factor radius))
  where
  terms-path :
    powerSeriesDifferenceFactorOnClosedRadius
      (λ n → a n Add.+ b n) (Real.ιℚ (fst radius))
      ≡
    (λ point n →
      powerSeriesDifferenceFactorOnClosedRadius
        a (Real.ιℚ (fst radius)) point n
        Add.+
      powerSeriesDifferenceFactorOnClosedRadius
        b (Real.ιℚ (fst radius)) point n)
  terms-path = funExt λ point → funExt λ n →
    mul-distrib-over-add-left
      (a (suc n)) (b (suc n))
      (powerDifferenceFactor
        (closedAbsRadiusPairLeft
          (Real.ιℚ (fst radius)) point)
        (closedAbsRadiusPairRight
          (Real.ιℚ (fst radius)) point)
        n)


scaleLocallyUniformPowerSeriesDifferenceFactor : ∀ c coefficients →
  LocallyUniformPowerSeriesDifferenceFactor coefficients →
  LocallyUniformPowerSeriesDifferenceFactor
    (scaleSeries c coefficients)
scaleLocallyUniformPowerSeriesDifferenceFactor
  c coefficients factor-local radius =
  subst
    (UniformlyCauchySeries
      (ClosedAbsRadiusPair (Real.ιℚ (fst radius))))
    (sym terms-path)
    (scaleUniformlyCauchySeries
      (ClosedAbsRadiusPair (Real.ιℚ (fst radius))) c
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients (Real.ιℚ (fst radius)))
      (factor-local radius))
  where
  terms-path :
    powerSeriesDifferenceFactorOnClosedRadius
      (scaleSeries c coefficients) (Real.ιℚ (fst radius))
      ≡
    (λ point →
      scaleSeries c
        (powerSeriesDifferenceFactorOnClosedRadius
          coefficients (Real.ιℚ (fst radius)) point))
  terms-path = funExt λ point → funExt λ n →
    sym (mul-assoc
      c (coefficients (suc n))
      (powerDifferenceFactor
        (closedAbsRadiusPairLeft
          (Real.ιℚ (fst radius)) point)
        (closedAbsRadiusPairRight
          (Real.ιℚ (fst radius)) point)
        n))


-- These value laws are stated for the opaque canonical whole-line evaluator.
-- They use uniqueness of the sum rather than unfolding the Archimedean-radius
-- construction, so they remain cheap and stable for downstream elaboration.

locallyUniformPowerSeriesValue-add :
  ∀ a b a-local b-local x →
  locallyUniformPowerSeriesValue
      (λ n → a n Add.+ b n)
      (addLocallyUniformPowerSeries a b a-local b-local) x
    ≡
  locallyUniformPowerSeriesValue a a-local x Add.+
    locallyUniformPowerSeriesValue b b-local x
locallyUniformPowerSeriesValue-add a b a-local b-local x =
  cong fst
    (isPropSummable target-terms canonical-sum additive-sum)
  where
  target-terms : RealSequence
  target-terms =
    powerSeriesTerms (λ n → a n Add.+ b n) x

  target-value : Real.ℝ
  target-value =
    locallyUniformPowerSeriesValue a a-local x Add.+
    locallyUniformPowerSeriesValue b b-local x

  canonical-sum : Summable target-terms
  canonical-sum =
    locallyUniformPowerSeriesValue
      (λ n → a n Add.+ b n)
      (addLocallyUniformPowerSeries a b a-local b-local) x
    , locallyUniformPowerSeriesValueHasSum
        (λ n → a n Add.+ b n)
        (addLocallyUniformPowerSeries a b a-local b-local) x

  pointwise-additive-sum :
    HasSum
      (λ n →
        powerSeriesTerms a x n Add.+ powerSeriesTerms b x n)
      target-value
  pointwise-additive-sum =
    snd (addSummable
      (powerSeriesTerms a x) (powerSeriesTerms b x)
      (locallyUniformPowerSeriesValue a a-local x
        , locallyUniformPowerSeriesValueHasSum a a-local x)
      (locallyUniformPowerSeriesValue b b-local x
        , locallyUniformPowerSeriesValueHasSum b b-local x))

  additive-sum : Summable target-terms
  additive-sum = target-value ,
    subst (λ terms → HasSum terms target-value)
      (sym (powerSeriesTerms-add-sequence a b x))
      pointwise-additive-sum


locallyUniformPowerSeriesValue-scale :
  ∀ c coefficients local x →
  locallyUniformPowerSeriesValue
      (scaleSeries c coefficients)
      (scaleLocallyUniformPowerSeries c coefficients local) x
    ≡
  c Mul.· locallyUniformPowerSeriesValue coefficients local x
locallyUniformPowerSeriesValue-scale c coefficients local x =
  cong fst
    (isPropSummable target-terms canonical-sum scaled-sum)
  where
  target-terms : RealSequence
  target-terms =
    powerSeriesTerms (scaleSeries c coefficients) x

  target-value : Real.ℝ
  target-value =
    c Mul.· locallyUniformPowerSeriesValue coefficients local x

  canonical-sum : Summable target-terms
  canonical-sum =
    locallyUniformPowerSeriesValue
      (scaleSeries c coefficients)
      (scaleLocallyUniformPowerSeries c coefficients local) x
    , locallyUniformPowerSeriesValueHasSum
        (scaleSeries c coefficients)
        (scaleLocallyUniformPowerSeries c coefficients local) x

  pointwise-scaled-sum :
    HasSum
      (scaleSeries c (powerSeriesTerms coefficients x))
      target-value
  pointwise-scaled-sum =
    scaleHasSum c (powerSeriesTerms coefficients x)
      (locallyUniformPowerSeriesValue coefficients local x)
      (locallyUniformPowerSeriesValueHasSum coefficients local x)

  scaled-sum : Summable target-terms
  scaled-sum = target-value ,
    subst (λ terms → HasSum terms target-value)
      (sym (powerSeriesTerms-scale-sequence c coefficients x))
      pointwise-scaled-sum

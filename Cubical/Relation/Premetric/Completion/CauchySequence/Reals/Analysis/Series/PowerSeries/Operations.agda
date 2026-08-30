module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Operations where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base


powerSeriesTerms-add-sequence :
  ∀ (a b : RealSequence) (x : Real.ℝ) →
  powerSeriesTerms (λ n → a n Add.+ b n) x ≡
  (λ n →
    powerSeriesTerms a x n Add.+ powerSeriesTerms b x n)
powerSeriesTerms-add-sequence a b x =
  funExt (powerSeriesTerms-add a b x)


powerSeriesTerms-scale-sequence :
  ∀ c (coefficients : RealSequence) x →
  powerSeriesTerms (scaleSeries c coefficients) x ≡
  scaleSeries c (powerSeriesTerms coefficients x)
powerSeriesTerms-scale-sequence c coefficients x =
  funExt (powerSeriesTerms-scale c coefficients x)


powerSeriesAddSummable : ∀ (a b : RealSequence) x →
  PowerSeriesSummableAt a x →
  PowerSeriesSummableAt b x →
  PowerSeriesSummableAt (λ n → a n Add.+ b n) x
powerSeriesAddSummable a b x a-summable b-summable =
  subst Summable
    (sym (powerSeriesTerms-add-sequence a b x))
    (addSummable
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-summable b-summable)


powerSeriesScaleSummable : ∀ c coefficients x →
  PowerSeriesSummableAt coefficients x →
  PowerSeriesSummableAt (scaleSeries c coefficients) x
powerSeriesScaleSummable c coefficients x summable =
  subst Summable
    (sym (powerSeriesTerms-scale-sequence c coefficients x))
    (scaleSummable c (powerSeriesTerms coefficients x) summable)


powerSeriesValue-add : ∀ (a b : RealSequence) x →
  (a-summable : PowerSeriesSummableAt a x) →
  (b-summable : PowerSeriesSummableAt b x) →
  (sum-summable :
    PowerSeriesSummableAt (λ n → a n Add.+ b n) x) →
  powerSeriesValue
      (λ n → a n Add.+ b n) x sum-summable
    ≡
  powerSeriesValue a x a-summable Add.+
    powerSeriesValue b x b-summable
powerSeriesValue-add
    a b x a-summable b-summable sum-summable =
  seriesSumIndependent sum-terms sum-summable target-summable
  where
  sum-terms : RealSequence
  sum-terms = powerSeriesTerms (λ n → a n Add.+ b n) x

  target : Real.ℝ
  target =
    powerSeriesValue a x a-summable Add.+
    powerSeriesValue b x b-summable

  pointwise-sum-has-sum :
    HasSum
      (λ n →
        powerSeriesTerms a x n Add.+ powerSeriesTerms b x n)
      target
  pointwise-sum-has-sum =
    seriesSumHasSum _
      (addSummable
        (powerSeriesTerms a x)
        (powerSeriesTerms b x)
        a-summable b-summable)

  sum-has-sum : HasSum sum-terms target
  sum-has-sum =
    subst (λ terms → HasSum terms target)
      (sym (powerSeriesTerms-add-sequence a b x))
      pointwise-sum-has-sum

  target-summable : Summable sum-terms
  target-summable = target , sum-has-sum


powerSeriesValue-scale : ∀ c coefficients x →
  (summable : PowerSeriesSummableAt coefficients x) →
  (scaled-summable :
    PowerSeriesSummableAt (scaleSeries c coefficients) x) →
  powerSeriesValue
      (scaleSeries c coefficients) x scaled-summable
    ≡
  c Mul.· powerSeriesValue coefficients x summable
powerSeriesValue-scale
    c coefficients x summable scaled-summable =
  seriesSumIndependent scaled-terms scaled-summable target-summable
  where
  scaled-terms : RealSequence
  scaled-terms =
    powerSeriesTerms (scaleSeries c coefficients) x

  target : Real.ℝ
  target = c Mul.· powerSeriesValue coefficients x summable

  pointwise-scaled-has-sum :
    HasSum (scaleSeries c (powerSeriesTerms coefficients x)) target
  pointwise-scaled-has-sum =
    seriesSumHasSum _
      (scaleSummable c (powerSeriesTerms coefficients x) summable)

  scaled-has-sum : HasSum scaled-terms target
  scaled-has-sum =
    subst (λ terms → HasSum terms target)
      (sym (powerSeriesTerms-scale-sequence c coefficients x))
      pointwise-scaled-has-sum

  target-summable : Summable scaled-terms
  target-summable = target , scaled-has-sum

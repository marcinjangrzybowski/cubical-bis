module Cubical.Analysis.Real.Series.PowerSeries.Operations where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.PowerSeries.Base


powerSeriesAddSummable : ∀ a b x →
  PowerSeriesSummableAt a x →
  PowerSeriesSummableAt b x →
  PowerSeriesSummableAt (λ n → a n + b n) x
powerSeriesAddSummable a b x a-summable b-summable =
  subst Summable
    (funExt (λ n → sym (powerSeriesTerms-add a b x n)))
    (addSummable
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-summable b-summable)


powerSeriesScaleSummable : ∀ c coefficients x →
  PowerSeriesSummableAt coefficients x →
  PowerSeriesSummableAt (scaleSeries c coefficients) x
powerSeriesScaleSummable c coefficients x summable =
  subst Summable
    (sym (funExt (powerSeriesTerms-scale c coefficients x)))
    (scaleSummable c (powerSeriesTerms coefficients x) summable)


powerSeriesValue-add : ∀ a b x
  (a-summable : PowerSeriesSummableAt a x)
  (b-summable : PowerSeriesSummableAt b x)
  (sum-summable :
    PowerSeriesSummableAt (λ n → a n + b n) x) →
  powerSeriesValue (λ n → a n + b n) x sum-summable ≡
  powerSeriesValue a x a-summable
    + powerSeriesValue b x b-summable
powerSeriesValue-add a b x a-summable b-summable sum-summable =
  seriesSumPresPath
    (powerSeriesTerms (λ n → a n + b n) x)
    (λ n → powerSeriesTerms a x n + powerSeriesTerms b x n)
    (funExt (powerSeriesTerms-add a b x))
    sum-summable
    (addSummable
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-summable b-summable)
  ∙ seriesSum-add
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-summable b-summable
      (addSummable
        (powerSeriesTerms a x)
        (powerSeriesTerms b x)
        a-summable b-summable)


powerSeriesValue-scale : ∀ c coefficients x
  (summable : PowerSeriesSummableAt coefficients x)
  (scaled-summable :
    PowerSeriesSummableAt (scaleSeries c coefficients) x) →
  powerSeriesValue (scaleSeries c coefficients) x scaled-summable ≡
  c · powerSeriesValue coefficients x summable
powerSeriesValue-scale c coefficients x summable scaled-summable =
  seriesSumPresPath
    (powerSeriesTerms (scaleSeries c coefficients) x)
    (scaleSeries c (powerSeriesTerms coefficients x))
    (funExt (powerSeriesTerms-scale c coefficients x))
    scaled-summable
    (scaleSummable c (powerSeriesTerms coefficients x) summable)
  ∙ seriesSum-scale
      c (powerSeriesTerms coefficients x)
      summable
      (scaleSummable c (powerSeriesTerms coefficients x) summable)

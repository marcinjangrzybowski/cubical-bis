module Cubical.Analysis.Real.Series.PowerSeries.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Functions.Powers using (powℝ)
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.PowerSeries.Base

open PositiveRationals using (ℚ₊; _+₊_; _·₊_)


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  positiveRationalNonnegative : ∀ bound →
    0ℝ ≤ℝ rat (fst bound)
  positiveRationalNonnegative bound =
    <ℝ-weaken 0ℝ (rat (fst bound))
      (<ℚ→<ℝ 0 (fst bound) (snd bound))


powerSeriesTerms-add-path : ∀ a b x →
  powerSeriesTerms (λ n → a n + b n) x ≡
  (λ n → powerSeriesTerms a x n + powerSeriesTerms b x n)
powerSeriesTerms-add-path a b x =
  funExt (powerSeriesTerms-add a b x)


powerSeriesTerms-scale-path : ∀ c coefficients x →
  powerSeriesTerms (scaleSeries c coefficients) x ≡
  scaleSeries c (powerSeriesTerms coefficients x)
powerSeriesTerms-scale-path c coefficients x =
  funExt (powerSeriesTerms-scale c coefficients x)


powerSeriesTerms-neg : ∀ coefficients x n →
  powerSeriesTerms (-_ ∘ coefficients) x n ≡
  - powerSeriesTerms coefficients x n
powerSeriesTerms-neg coefficients x n =
  ℝRing.-DistL· (coefficients n) (powℝ x n)


powerSeriesTerms-neg-path : ∀ coefficients x →
  powerSeriesTerms (-_ ∘ coefficients) x ≡
  (-_ ∘ powerSeriesTerms coefficients x)
powerSeriesTerms-neg-path coefficients x =
  funExt (powerSeriesTerms-neg coefficients x)


powerSeriesTerms-sub : ∀ a b x n →
  powerSeriesTerms (λ k → a k - b k) x n ≡
  powerSeriesTerms a x n - powerSeriesTerms b x n
powerSeriesTerms-sub a b x n =
  powerSeriesTerms-add a (-_ ∘ b) x n
  ∙ cong (powerSeriesTerms a x n +_)
      (powerSeriesTerms-neg b x n)


powerSeriesTerms-sub-path : ∀ a b x →
  powerSeriesTerms (λ n → a n - b n) x ≡
  (λ n → powerSeriesTerms a x n - powerSeriesTerms b x n)
powerSeriesTerms-sub-path a b x =
  funExt (powerSeriesTerms-sub a b x)


coefficientAbsBound-neg : ∀ bound coefficients →
  CoefficientAbsBound bound coefficients →
  CoefficientAbsBound bound (-_ ∘ coefficients)
coefficientAbsBound-neg bound coefficients bounded n =
  subst
    (_≤ℝ rat (fst bound))
    (sym (absNeg (coefficients n)))
    (bounded n)


coefficientAbsBound-add : ∀ leftBound rightBound a b →
  CoefficientAbsBound leftBound a →
  CoefficientAbsBound rightBound b →
  CoefficientAbsBound
    (leftBound +₊ rightBound) (λ n → a n + b n)
coefficientAbsBound-add
    leftBound rightBound a b aBounded bBounded n =
  ≤ℝ-trans
    (absℝ (a n + b n))
    (absℝ (a n) + absℝ (b n))
    (rat (fst (leftBound +₊ rightBound)))
    (absTriangle (a n) (b n))
    (subst
      ((absℝ (a n) + absℝ (b n)) ≤ℝ_)
      (rat+rat (fst leftBound) (fst rightBound))
      (addPres≤
        (absℝ (a n)) (rat (fst leftBound))
        (absℝ (b n)) (rat (fst rightBound))
        (aBounded n) (bBounded n)))


coefficientAbsBound-sub : ∀ leftBound rightBound a b →
  CoefficientAbsBound leftBound a →
  CoefficientAbsBound rightBound b →
  CoefficientAbsBound
    (leftBound +₊ rightBound) (λ n → a n - b n)
coefficientAbsBound-sub
    leftBound rightBound a b aBounded bBounded =
  coefficientAbsBound-add
    leftBound rightBound a (-_ ∘ b)
    aBounded
    (coefficientAbsBound-neg rightBound b bBounded)


coefficientAbsBound-scale : ∀ scalarBound bound scalar coefficients →
  absℝ scalar ≤ℝ rat (fst scalarBound) →
  CoefficientAbsBound bound coefficients →
  CoefficientAbsBound
    (scalarBound ·₊ bound) (scaleSeries scalar coefficients)
coefficientAbsBound-scale
    scalarBound bound scalar coefficients
    scalarBounded coefficientsBounded n =
  subst
    (absℝ (scaleSeries scalar coefficients n) ≤ℝ_)
    (mul-rat (fst scalarBound) (fst bound))
    (subst
      (_≤ℝ rat (fst scalarBound) · rat (fst bound))
      (sym (absMul scalar (coefficients n)))
      (mulPres≤
        (absℝ scalar) (rat (fst scalarBound))
        (absℝ (coefficients n)) (rat (fst bound))
        (positiveRationalNonnegative scalarBound)
        (absNonnegative (coefficients n))
        scalarBounded (coefficientsBounded n)))


powerSeriesAddSummable : ∀ a b x →
  PowerSeriesSummableAt a x →
  PowerSeriesSummableAt b x →
  PowerSeriesSummableAt (λ n → a n + b n) x
powerSeriesAddSummable a b x a-summable b-summable =
  subst Summable
    (sym (powerSeriesTerms-add-path a b x))
    (addSummable
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-summable b-summable)


powerSeriesNegSummable : ∀ coefficients x →
  PowerSeriesSummableAt coefficients x →
  PowerSeriesSummableAt (-_ ∘ coefficients) x
powerSeriesNegSummable coefficients x summable =
  subst Summable
    (sym (powerSeriesTerms-neg-path coefficients x))
    (negSummable (powerSeriesTerms coefficients x) summable)


powerSeriesSubSummable : ∀ a b x →
  PowerSeriesSummableAt a x →
  PowerSeriesSummableAt b x →
  PowerSeriesSummableAt (λ n → a n - b n) x
powerSeriesSubSummable a b x a-summable b-summable =
  subst Summable
    (sym (powerSeriesTerms-sub-path a b x))
    (subSummable
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-summable b-summable)


powerSeriesScaleSummable : ∀ c coefficients x →
  PowerSeriesSummableAt coefficients x →
  PowerSeriesSummableAt (scaleSeries c coefficients) x
powerSeriesScaleSummable c coefficients x summable =
  subst Summable
    (sym (powerSeriesTerms-scale-path c coefficients x))
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
    (powerSeriesTerms-add-path a b x)
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


powerSeriesValue-neg : ∀ coefficients x
  (summable : PowerSeriesSummableAt coefficients x)
  (neg-summable :
    PowerSeriesSummableAt (-_ ∘ coefficients) x) →
  powerSeriesValue (-_ ∘ coefficients) x neg-summable ≡
  - powerSeriesValue coefficients x summable
powerSeriesValue-neg
    coefficients x summable neg-summable =
  seriesSumPresPath
    (powerSeriesTerms (-_ ∘ coefficients) x)
    (-_ ∘ powerSeriesTerms coefficients x)
    (powerSeriesTerms-neg-path coefficients x)
    neg-summable
    (negSummable (powerSeriesTerms coefficients x) summable)
  ∙ seriesSum-neg
      (powerSeriesTerms coefficients x)
      summable
      (negSummable (powerSeriesTerms coefficients x) summable)


powerSeriesValue-sub : ∀ a b x
  (a-summable : PowerSeriesSummableAt a x)
  (b-summable : PowerSeriesSummableAt b x)
  (difference-summable :
    PowerSeriesSummableAt (λ n → a n - b n) x) →
  powerSeriesValue (λ n → a n - b n) x
      difference-summable
    ≡
  powerSeriesValue a x a-summable
    - powerSeriesValue b x b-summable
powerSeriesValue-sub
    a b x a-summable b-summable difference-summable =
  seriesSumPresPath
    (powerSeriesTerms (λ n → a n - b n) x)
    (λ n → powerSeriesTerms a x n - powerSeriesTerms b x n)
    (powerSeriesTerms-sub-path a b x)
    difference-summable
    (subSummable
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-summable b-summable)
  ∙ seriesSum-sub
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-summable b-summable
      (subSummable
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
    (powerSeriesTerms-scale-path c coefficients x)
    scaled-summable
    (scaleSummable c (powerSeriesTerms coefficients x) summable)
  ∙ seriesSum-scale
      c (powerSeriesTerms coefficients x)
      summable
      (scaleSummable c (powerSeriesTerms coefficients x) summable)

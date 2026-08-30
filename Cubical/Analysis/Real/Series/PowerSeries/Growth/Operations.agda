module Cubical.Analysis.Real.Series.PowerSeries.Growth.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.PowerSeries.Growth

open PositiveRationals using (ℚ₊; _+₊_; _·₊_)


private
  positiveRationalNonnegative : ∀ q →
    0ℝ ≤ℝ rat (fst q)
  positiveRationalNonnegative q =
    <ℝ-weaken 0ℝ (rat (fst q))
      (<ℚ→<ℝ 0 (fst q) (snd q))


coefficientGrowthBound-neg : ∀ bound growth coefficients →
  CoefficientGrowthBound bound growth coefficients →
  CoefficientGrowthBound bound growth (-_ ∘ coefficients)
coefficientGrowthBound-neg
    bound growth coefficients coefficients-bounded n =
  subst
    (_≤ℝ rat (fst bound) · powℝ (rat (fst growth)) n)
    (sym (absNeg (coefficients n)))
    (coefficients-bounded n)


coefficientGrowthBound-add : ∀ left-bound right-bound growth a b →
  CoefficientGrowthBound left-bound growth a →
  CoefficientGrowthBound right-bound growth b →
  CoefficientGrowthBound
    (left-bound +₊ right-bound) growth
    (λ n → a n + b n)
coefficientGrowthBound-add
    left-bound right-bound growth a b
    a-bounded b-bounded n =
  ≤ℝ-trans
    (absℝ (a n + b n))
    (absℝ (a n) + absℝ (b n))
    (rat (fst (left-bound +₊ right-bound)) · growth-power)
    (absTriangle (a n) (b n))
    (subst
      ((absℝ (a n) + absℝ (b n)) ≤ℝ_)
      upper-path
      (addPres≤
        (absℝ (a n)) (rat (fst left-bound) · growth-power)
        (absℝ (b n)) (rat (fst right-bound) · growth-power)
        (a-bounded n) (b-bounded n)))
  where
  growth-power : ℝ
  growth-power = powℝ (rat (fst growth)) n

  upper-path :
    rat (fst left-bound) · growth-power
      + rat (fst right-bound) · growth-power
      ≡
    rat (fst (left-bound +₊ right-bound)) · growth-power
  upper-path =
    sym
      (mulDistL
        (rat (fst left-bound))
        (rat (fst right-bound)) growth-power)
    ∙ cong
        (_· growth-power)
        (rat+rat (fst left-bound) (fst right-bound))


coefficientGrowthBound-sub : ∀ left-bound right-bound growth a b →
  CoefficientGrowthBound left-bound growth a →
  CoefficientGrowthBound right-bound growth b →
  CoefficientGrowthBound
    (left-bound +₊ right-bound) growth
    (λ n → a n - b n)
coefficientGrowthBound-sub
    left-bound right-bound growth a b
    a-bounded b-bounded =
  coefficientGrowthBound-add
    left-bound right-bound growth a (-_ ∘ b)
    a-bounded
    (coefficientGrowthBound-neg
      right-bound growth b b-bounded)


coefficientGrowthBound-scale : ∀ scalar-bound bound growth scalar coefficients →
  absℝ scalar ≤ℝ rat (fst scalar-bound) →
  CoefficientGrowthBound bound growth coefficients →
  CoefficientGrowthBound
    (scalar-bound ·₊ bound) growth
    (scaleSeries scalar coefficients)
coefficientGrowthBound-scale
    scalar-bound bound growth scalar coefficients
    scalar-bounded coefficients-bounded n =
  subst
    (absℝ (scaleSeries scalar coefficients n) ≤ℝ_)
    upper-path
    (subst
      (_≤ℝ
        rat (fst scalar-bound) ·
          (rat (fst bound) · growth-power))
      (sym (absMul scalar (coefficients n)))
      (mulPres≤
        (absℝ scalar) (rat (fst scalar-bound))
        (absℝ (coefficients n))
        (rat (fst bound) · growth-power)
        (positiveRationalNonnegative scalar-bound)
        (absNonnegative (coefficients n))
        scalar-bounded (coefficients-bounded n)))
  where
  growth-power : ℝ
  growth-power = powℝ (rat (fst growth)) n

  upper-path :
    rat (fst scalar-bound) ·
        (rat (fst bound) · growth-power)
      ≡
    rat (fst (scalar-bound ·₊ bound)) · growth-power
  upper-path =
    mulAssoc
      (rat (fst scalar-bound))
      (rat (fst bound)) growth-power
    ∙ cong
        (_· growth-power)
        (mul-rat (fst scalar-bound) (fst bound))

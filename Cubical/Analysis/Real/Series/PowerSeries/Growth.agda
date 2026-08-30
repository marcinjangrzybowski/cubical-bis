module Cubical.Analysis.Real.Series.PowerSeries.Growth where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Comparison
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Bounds
open import Cubical.Analysis.Real.Series.PowerSeries.Convergence

open PositiveRationals using (ℚ₊; _·₊_)


CoefficientGrowthBound :
  ℚ₊ → ℚ₊ → RealSequence → Type₀
CoefficientGrowthBound bound growth coefficients =
  ∀ n →
  absℝ (coefficients n) ≤ℝ
  rat (fst bound) · powℝ (rat (fst growth)) n


private
  positiveRationalNonnegative : ∀ q →
    0ℝ ≤ℝ rat (fst q)
  positiveRationalNonnegative q =
    <ℝ-weaken 0ℝ (rat (fst q))
      (<ℚ→<ℝ 0 (fst q) (snd q))

  reorderFourFactors : ∀ (x y u v : ℝ) →
    (x · y) · (u · v) ≡ (x · u) · (y · v)
  reorderFourFactors x y u v =
    mulAssoc (x · y) u v
    ∙ cong (_· v)
        ( sym (mulAssoc x y u)
        ∙ cong (x ·_) (mulComm y u)
        ∙ mulAssoc x u y
        )
    ∙ sym (mulAssoc (x · u) y v)

  powMul : ∀ x y n →
    powℝ (x · y) n ≡ powℝ x n · powℝ y n
  powMul x y zero =
    sym (mulIdL 1ℝ)
  powMul x y (suc n) =
    cong ((x · y) ·_) (powMul x y n)
    ∙ reorderFourFactors
        x y (powℝ x n) (powℝ y n)


growthRadius : ℚ₊ → ℚ₊ → ℚ₊
growthRadius growth radius = growth ·₊ radius


coefficientGrowthMajorant :
  ℚ₊ → ℚ₊ → ℚ₊ → RealSequence
coefficientGrowthMajorant bound growth radius =
  coefficientGeometricMajorant
    bound (growthRadius growth radius)


powerSeriesTermAbsBoundByGrowth :
  ∀ bound growth radius coefficients x →
  CoefficientGrowthBound bound growth coefficients →
  absℝ x ≤ℝ rat (fst radius) →
  ∀ n →
  absℝ (powerSeriesTerms coefficients x n) ≤ℝ
  coefficientGrowthMajorant bound growth radius n
powerSeriesTermAbsBoundByGrowth
    bound growth radius coefficients x
    coefficients-bounded absx≤radius n =
  subst
    (absℝ (powerSeriesTerms coefficients x n) ≤ℝ_)
    upperPath productBound
  where
  coefficientPower : ℝ
  coefficientPower = powℝ (rat (fst growth)) n

  radiusPower : ℝ
  radiusPower = powℝ (rat (fst radius)) n

  absoluteInputPower : ℝ
  absoluteInputPower = powℝ (absℝ x) n

  absoluteTermPath :
    absℝ (powerSeriesTerms coefficients x n) ≡
    absℝ (coefficients n) · absoluteInputPower
  absoluteTermPath =
    absMul (coefficients n) (powℝ x n)
    ∙ cong (absℝ (coefficients n) ·_) (absPow x n)

  powerBound : absoluteInputPower ≤ℝ radiusPower
  powerBound =
    powMono n (absNonnegative x) absx≤radius

  coefficientUpper : ℝ
  coefficientUpper = rat (fst bound) · coefficientPower

  coefficientUpperNonnegative :
    0ℝ ≤ℝ coefficientUpper
  coefficientUpperNonnegative =
    isNonnegative→0≤ coefficientUpper
      (mulPresIsNonnegative
        (rat (fst bound)) coefficientPower
        (0≤→isNonnegative
          (rat (fst bound))
          (positiveRationalNonnegative bound))
        (0≤→isNonnegative coefficientPower
          (powNonnegative
            (rat (fst growth)) n
            (positiveRationalNonnegative growth))))

  rawProductBound :
    absℝ (coefficients n) · absoluteInputPower ≤ℝ
    coefficientUpper · radiusPower
  rawProductBound =
    mulPres≤
      (absℝ (coefficients n)) coefficientUpper
      absoluteInputPower radiusPower
      coefficientUpperNonnegative
      (powNonnegative
        (absℝ x) n (absNonnegative x))
      (coefficients-bounded n) powerBound

  ratioPath :
    rat (fst (growthRadius growth radius)) ≡
    rat (fst growth) · rat (fst radius)
  ratioPath =
    sym (mul-rat (fst growth) (fst radius))

  upperPath :
    coefficientUpper · radiusPower ≡
    coefficientGrowthMajorant bound growth radius n
  upperPath =
    sym (mulAssoc
      (rat (fst bound)) coefficientPower radiusPower
    )
    ∙ cong (rat (fst bound) ·_)
        ( sym
            (powMul
              (rat (fst growth))
              (rat (fst radius)) n)
        ∙ cong (λ ratio → powℝ ratio n)
            (sym ratioPath)
        )

  productBound :
    absℝ (powerSeriesTerms coefficients x n) ≤ℝ
    coefficientUpper · radiusPower
  productBound =
    subst
      (_≤ℝ coefficientUpper · radiusPower)
      (sym absoluteTermPath)
      rawProductBound


powerSeriesIsAbsolutelyCauchyByGrowth :
  ∀ bound growth radius coefficients x →
  CoefficientGrowthBound bound growth coefficients →
  absℝ x ≤ℝ rat (fst radius) →
  fst (growthRadius growth radius) ℚ.< 1 →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelyCauchyByGrowth
    bound growth radius coefficients x
    coefficients-bounded absx≤radius combined<1 =
  dominatedCauchySeriesIsCauchy
    (absℝ ∘ powerSeriesTerms coefficients x)
    (coefficientGrowthMajorant bound growth radius)
    dominates
    (coefficientGeometricMajorantIsCauchyByStrictRadius
      bound (growthRadius growth radius) combined<1)
  where
  dominates : ∀ n →
    absℝ (absℝ (powerSeriesTerms coefficients x n)) ≤ℝ
    coefficientGrowthMajorant bound growth radius n
  dominates n =
    subst
      (_≤ℝ coefficientGrowthMajorant bound growth radius n)
      (sym (absIdem (powerSeriesTerms coefficients x n)))
      (powerSeriesTermAbsBoundByGrowth
        bound growth radius coefficients x
        coefficients-bounded absx≤radius n)


powerSeriesIsCauchyByGrowth :
  ∀ bound growth radius coefficients x →
  CoefficientGrowthBound bound growth coefficients →
  absℝ x ≤ℝ rat (fst radius) →
  fst (growthRadius growth radius) ℚ.< 1 →
  IsCauchySeries (powerSeriesTerms coefficients x)
powerSeriesIsCauchyByGrowth
    bound growth radius coefficients x
    coefficients-bounded absx≤radius combined<1 =
  absoluteCauchySeriesIsCauchy
    (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchyByGrowth
      bound growth radius coefficients x
      coefficients-bounded absx≤radius combined<1)


powerSeriesIsSummableByGrowth :
  ∀ bound growth radius coefficients x →
  CoefficientGrowthBound bound growth coefficients →
  absℝ x ≤ℝ rat (fst radius) →
  fst (growthRadius growth radius) ℚ.< 1 →
  PowerSeriesSummableAt coefficients x
powerSeriesIsSummableByGrowth
    bound growth radius coefficients x
    coefficients-bounded absx≤radius combined<1 =
  absoluteCauchySeriesIsSummable
    (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchyByGrowth
      bound growth radius coefficients x
      coefficients-bounded absx≤radius combined<1)


powerSeriesValueAbsBoundByGrowth :
  ∀ bound growth radius coefficients x
  (coefficients-bounded :
    CoefficientGrowthBound bound growth coefficients)
  (absx≤radius : absℝ x ≤ℝ rat (fst radius))
  (combined<1 : fst (growthRadius growth radius) ℚ.< 1) →
  absℝ
    (powerSeriesValue coefficients x
      (powerSeriesIsSummableByGrowth
        bound growth radius coefficients x
        coefficients-bounded absx≤radius combined<1))
    ≤ℝ
  seriesSum
    (coefficientGrowthMajorant bound growth radius)
    (coefficientGeometricMajorantSummableByStrictRadius
      bound (growthRadius growth radius) combined<1)
powerSeriesValueAbsBoundByGrowth
    bound growth radius coefficients x
    coefficients-bounded absx≤radius combined<1 =
  seriesSumAbsBoundBy
    (powerSeriesTerms coefficients x)
    (coefficientGrowthMajorant bound growth radius)
    (powerSeriesIsSummableByGrowth
      bound growth radius coefficients x
      coefficients-bounded absx≤radius combined<1)
    (coefficientGeometricMajorantSummableByStrictRadius
      bound (growthRadius growth radius) combined<1)
    (powerSeriesTermAbsBoundByGrowth
      bound growth radius coefficients x
      coefficients-bounded absx≤radius)

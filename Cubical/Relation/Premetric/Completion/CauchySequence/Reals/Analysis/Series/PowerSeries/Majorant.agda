module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul ; nonnegative→abs-self ; mul-monotone-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_ ; <ℝ-weaken)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Order
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base


CoefficientMajorizedBy : RealSequence → RealSequence → Type₀
CoefficientMajorizedBy coefficients majorant =
  ∀ n → Abs.absℝ (coefficients n) ≤ℝ majorant n


NonnegativeCoefficients : RealSequence → Type₀
NonnegativeCoefficients coefficients =
  ∀ n → zeroℝ ≤ℝ coefficients n


-- Nonnegativity need not be supplied separately for a majorant: it follows
-- from the coefficient bound itself.  This removes a redundant hypothesis
-- present in the older Cauchy-real power-series interface.

coefficientMajorantIsNonnegative : ∀ coefficients majorant →
  CoefficientMajorizedBy coefficients majorant →
  NonnegativeCoefficients majorant
coefficientMajorantIsNonnegative coefficients majorant majorizes n =
  ≤ℝ-trans zeroℝ (Abs.absℝ (coefficients n)) (majorant n)
    (zero≤abs (coefficients n)) (majorizes n)


nonnegativeCoefficientsSelfMajorized : ∀ coefficients →
  NonnegativeCoefficients coefficients →
  CoefficientMajorizedBy coefficients coefficients
nonnegativeCoefficientsSelfMajorized coefficients nonnegative n =
  subst (_≤ℝ coefficients n)
    (sym (nonnegative→abs-self
      (coefficients n) (nonnegative n)))
    (≤ℝ-refl (coefficients n))


powerSeriesTermAbsBoundByCoefficientMajorant :
  ∀ coefficients majorant x radius →
  CoefficientMajorizedBy coefficients majorant →
  Abs.absℝ x ≤ℝ radius →
  ∀ n →
  Abs.absℝ (powerSeriesTerms coefficients x n) ≤ℝ
  powerSeriesTerms majorant radius n
powerSeriesTermAbsBoundByCoefficientMajorant
  coefficients majorant x radius coefficients-majorized absx≤radius n =
  subst (_≤ℝ powerSeriesTerms majorant radius n)
    (sym absolute-term-path) product-bound
  where
  absolute-term-path :
    Abs.absℝ (powerSeriesTerms coefficients x n) ≡
    Abs.absℝ (coefficients n) Mul.· Abs.absℝ x ^ⁿ n
  absolute-term-path =
    abs-mul (coefficients n) (x ^ⁿ n)
    ∙ cong (Abs.absℝ (coefficients n) Mul.·_) (absPow n x)

  radius-power-bound :
    Abs.absℝ x ^ⁿ n ≤ℝ radius ^ⁿ n
  radius-power-bound =
    powMono n (zero≤abs x) absx≤radius

  product-bound :
    Abs.absℝ (coefficients n) Mul.· Abs.absℝ x ^ⁿ n ≤ℝ
    powerSeriesTerms majorant radius n
  product-bound =
    mul-monotone-nonnegative
      (Abs.absℝ (coefficients n)) (majorant n)
      (Abs.absℝ x ^ⁿ n) (radius ^ⁿ n)
      (coefficients-majorized n) radius-power-bound
      (zero≤abs (coefficients n))
      (powNonnegative (Abs.absℝ x) n (zero≤abs x))


powerSeriesIsAbsolutelyCauchyByCoefficientMajorant :
  ∀ coefficients majorant x radius →
  CoefficientMajorizedBy coefficients majorant →
  Abs.absℝ x ≤ℝ radius →
  IsCauchySeries (powerSeriesTerms majorant radius) →
  IsAbsolutelyCauchySeries (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
  coefficients majorant x radius coefficients-majorized
  absx≤radius majorant-cauchy =
  dominatedCauchySeriesIsCauchy
    (Abs.absℝ ∘ powerSeriesTerms coefficients x)
    (powerSeriesTerms majorant radius)
    dominates majorant-cauchy
  where
  dominates : ∀ n →
    Abs.absℝ (Abs.absℝ (powerSeriesTerms coefficients x n)) ≤ℝ
    powerSeriesTerms majorant radius n
  dominates n =
    subst (_≤ℝ powerSeriesTerms majorant radius n)
      (sym (Abs.absℝ-idempotent
        (powerSeriesTerms coefficients x n)))
      (powerSeriesTermAbsBoundByCoefficientMajorant
        coefficients majorant x radius
        coefficients-majorized absx≤radius n)


powerSeriesIsCauchyByCoefficientMajorant :
  ∀ coefficients majorant x radius →
  CoefficientMajorizedBy coefficients majorant →
  Abs.absℝ x ≤ℝ radius →
  IsCauchySeries (powerSeriesTerms majorant radius) →
  IsCauchySeries (powerSeriesTerms coefficients x)
powerSeriesIsCauchyByCoefficientMajorant
  coefficients majorant x radius coefficients-majorized
  absx≤radius majorant-cauchy =
  absoluteCauchySeriesIsCauchy (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
      coefficients majorant x radius coefficients-majorized
      absx≤radius majorant-cauchy)


powerSeriesIsSummableByCoefficientMajorant :
  ∀ coefficients majorant x radius →
  CoefficientMajorizedBy coefficients majorant →
  Abs.absℝ x ≤ℝ radius →
  IsCauchySeries (powerSeriesTerms majorant radius) →
  PowerSeriesSummableAt coefficients x
powerSeriesIsSummableByCoefficientMajorant
  coefficients majorant x radius coefficients-majorized
  absx≤radius majorant-cauchy =
  absoluteCauchySeriesIsSummable (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
      coefficients majorant x radius coefficients-majorized
      absx≤radius majorant-cauchy)


nonnegativePowerSeriesIsAbsolutelyCauchyWithinRadius :
  ∀ coefficients inner-radius outer-radius →
  NonnegativeCoefficients coefficients →
  zeroℝ ≤ℝ inner-radius →
  inner-radius ≤ℝ outer-radius →
  IsCauchySeries (powerSeriesTerms coefficients outer-radius) →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms coefficients inner-radius)
nonnegativePowerSeriesIsAbsolutelyCauchyWithinRadius
  coefficients inner-radius outer-radius
  nonnegative inner-nonnegative inner≤outer outer-cauchy =
  powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
    coefficients coefficients inner-radius outer-radius
    (nonnegativeCoefficientsSelfMajorized coefficients nonnegative)
    abs-inner≤outer outer-cauchy
  where
  abs-inner≤outer : Abs.absℝ inner-radius ≤ℝ outer-radius
  abs-inner≤outer =
    subst (_≤ℝ outer-radius)
      (sym (nonnegative→abs-self inner-radius inner-nonnegative))
      inner≤outer


nonnegativePowerSeriesIsCauchyWithinRadius :
  ∀ coefficients inner-radius outer-radius →
  NonnegativeCoefficients coefficients →
  zeroℝ ≤ℝ inner-radius →
  inner-radius ≤ℝ outer-radius →
  IsCauchySeries (powerSeriesTerms coefficients outer-radius) →
  IsCauchySeries (powerSeriesTerms coefficients inner-radius)
nonnegativePowerSeriesIsCauchyWithinRadius
  coefficients inner-radius outer-radius
  nonnegative inner-nonnegative inner≤outer outer-cauchy =
  absoluteCauchySeriesIsCauchy
    (powerSeriesTerms coefficients inner-radius)
    (nonnegativePowerSeriesIsAbsolutelyCauchyWithinRadius
      coefficients inner-radius outer-radius
      nonnegative inner-nonnegative inner≤outer outer-cauchy)


nonnegativePowerSeriesIsCauchyWithinStrictRadius :
  ∀ coefficients inner-radius outer-radius →
  NonnegativeCoefficients coefficients →
  zeroℝ ≤ℝ inner-radius →
  inner-radius <ℝ outer-radius →
  IsCauchySeries (powerSeriesTerms coefficients outer-radius) →
  IsCauchySeries (powerSeriesTerms coefficients inner-radius)
nonnegativePowerSeriesIsCauchyWithinStrictRadius
  coefficients inner-radius outer-radius
  nonnegative inner-nonnegative inner<outer =
  nonnegativePowerSeriesIsCauchyWithinRadius
    coefficients inner-radius outer-radius nonnegative inner-nonnegative
    (<ℝ-weaken inner-radius outer-radius inner<outer)


powerSeriesAbsoluteSumLeCoefficientMajorant :
  ∀ coefficients majorant x radius →
  (coefficients-majorized :
    CoefficientMajorizedBy coefficients majorant) →
  (absx≤radius : Abs.absℝ x ≤ℝ radius) →
  (absolute :
    IsAbsolutelyCauchySeries (powerSeriesTerms coefficients x)) →
  (majorant-summable :
    Summable (powerSeriesTerms majorant radius)) →
  seriesSum (Abs.absℝ ∘ powerSeriesTerms coefficients x)
      (absoluteCauchySeriesIsAbsolutelySummable
        (powerSeriesTerms coefficients x) absolute) ≤ℝ
  seriesSum (powerSeriesTerms majorant radius) majorant-summable
powerSeriesAbsoluteSumLeCoefficientMajorant
  coefficients majorant x radius coefficients-majorized
  absx≤radius absolute majorant-summable =
  seriesSumMono
    (Abs.absℝ ∘ powerSeriesTerms coefficients x)
    (powerSeriesTerms majorant radius)
    (absoluteCauchySeriesIsAbsolutelySummable
      (powerSeriesTerms coefficients x) absolute)
    majorant-summable
    (powerSeriesTermAbsBoundByCoefficientMajorant
      coefficients majorant x radius
      coefficients-majorized absx≤radius)

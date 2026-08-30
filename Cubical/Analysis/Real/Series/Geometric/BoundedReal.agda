module Cubical.Analysis.Real.Series.Geometric.BoundedReal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Geometric.Base
open import Cubical.Analysis.Real.Series.Geometric.StrictRational


private
  module ℚOrder =
    OrderedCommRingTheory ℚOrderedCommRing


-- A rational contraction bound keeps the quantitative modulus explicit.  In
-- particular, it does not choose a rational bound from a merely real proof of
-- |q| < 1.
RationalContractionBound : ℝ → ℚ → Type₀
RationalContractionBound q r =
  (absℝ q ≤ℝ rat r) × (ℚOrder.abs r ℚ.< 1)


realGeometricPowerAbsBound : ∀ q r →
  absℝ q ≤ℝ rat r → ∀ n →
  absℝ (geometricTerms q n) ≤ℝ
  geometricTerms (rat r) n
realGeometricPowerAbsBound q r absq≤r n =
  subst
    (_≤ℝ geometricTerms (rat r) n)
    (sym (absPow q n))
    (powMono n (absNonnegative q) absq≤r)


realGeometricSeriesChosenCauchyByRationalBound : ∀ q r →
  RationalContractionBound q r →
  ChosenIsCauchySequence
    (partialSum (geometricTerms q))
realGeometricSeriesChosenCauchyByRationalBound
    q r (absq≤r , absr<1) =
  dominatedChosenCauchySeriesIsChosenCauchy
    (geometricTerms q)
    (geometricTerms (rat r))
    (realGeometricPowerAbsBound q r absq≤r)
    (strictSignedRationalGeometricSeriesChosenCauchy
      r absr<1)


realGeometricSeriesIsCauchyByRationalBound : ∀ q r →
  RationalContractionBound q r →
  IsCauchySeries (geometricTerms q)
realGeometricSeriesIsCauchyByRationalBound q r bound =
  ∣ realGeometricSeriesChosenCauchyByRationalBound
      q r bound ∣₁


realGeometricSeriesSummableByRationalBound : ∀ q r →
  RationalContractionBound q r →
  Summable (geometricTerms q)
realGeometricSeriesSummableByRationalBound q r bound =
  cauchySeriesIsSummable (geometricTerms q)
    (realGeometricSeriesIsCauchyByRationalBound
      q r bound)


realGeometricPowersTendToZeroByRationalBound : ∀ q r →
  (bound : RationalContractionBound q r) →
  isLimitSequence (geometricTerms q) 0ℝ
realGeometricPowersTendToZeroByRationalBound q r bound =
  summableTermsTendToZero (geometricTerms q)
    (realGeometricSeriesSummableByRationalBound
      q r bound)


realGeometricRatioLessThanOneByRationalBound : ∀ q r →
  RationalContractionBound q r → q <ℝ 1ℝ
realGeometricRatioLessThanOneByRationalBound
    q r (absq≤r , absr<1) =
  ≤<ℝ-trans q (absℝ q) 1ℝ
    (leAbs q)
    (≤<ℝ-trans
      (absℝ q) (rat r) 1ℝ
      absq≤r
      (<ℚ→<ℝ r 1
        (ℚ.isTrans≤< r (ℚOrder.abs r) 1
          (ℚOrder.≤abs r) absr<1)))


realGeometricPositiveDenominatorByRationalBound : ∀ q r →
  RationalContractionBound q r →
  0ℝ <ℝ 1ℝ - q
realGeometricPositiveDenominatorByRationalBound q r bound =
  positiveSub q 1ℝ
    (realGeometricRatioLessThanOneByRationalBound
      q r bound)


realGeometricSumByRationalBound : ∀ q r →
  RationalContractionBound q r → ℝ
realGeometricSumByRationalBound q r bound =
  positiveReciprocal (1ℝ - q)
    (realGeometricPositiveDenominatorByRationalBound
      q r bound)


realGeometricSeriesHasSumByRationalBound : ∀ q r →
  (bound : RationalContractionBound q r) →
  HasSum (geometricTerms q)
    (realGeometricSumByRationalBound q r bound)
realGeometricSeriesHasSumByRationalBound q r bound =
  subst
    (λ sequence → isLimitSequence sequence reciprocal)
    (funExt candidateEqualsPartial)
    candidateLimit
  where
  positiveDenominator : 0ℝ <ℝ 1ℝ - q
  positiveDenominator =
    realGeometricPositiveDenominatorByRationalBound
      q r bound

  reciprocal : ℝ
  reciprocal =
    realGeometricSumByRationalBound q r bound

  oneMinusPowers : RealSequence
  oneMinusPowers n = 1ℝ - geometricTerms q n

  oneMinusPowersLimit :
    isLimitSequence oneMinusPowers 1ℝ
  oneMinusPowersLimit =
    subst (isLimitSequence oneMinusPowers)
      (subZero 1ℝ)
      (subPresIsLimitSequence
        (constantIsLimitSequence 1ℝ)
        (realGeometricPowersTendToZeroByRationalBound
          q r bound))

  candidate : RealSequence
  candidate n = reciprocal · oneMinusPowers n

  candidateLimit :
    isLimitSequence candidate reciprocal
  candidateLimit =
    subst (isLimitSequence candidate)
      (mulIdR reciprocal)
      (mulPresIsLimitSequence
        (constantIsLimitSequence reciprocal)
        oneMinusPowersLimit)

  candidateEqualsPartial : ∀ n →
    candidate n ≡ partialSum (geometricTerms q) n
  candidateEqualsPartial n =
    sym
      (geometricPartialSumByReciprocal
        q n positiveDenominator)


seriesSum-realGeometricByRationalBound : ∀ q r →
  (bound : RationalContractionBound q r) →
  (summable : Summable (geometricTerms q)) →
  seriesSum (geometricTerms q) summable ≡
  realGeometricSumByRationalBound q r bound
seriesSum-realGeometricByRationalBound
    q r bound summable =
  seriesSumIndependent
    (geometricTerms q) summable
    ( realGeometricSumByRationalBound q r bound
    , realGeometricSeriesHasSumByRationalBound q r bound
    )

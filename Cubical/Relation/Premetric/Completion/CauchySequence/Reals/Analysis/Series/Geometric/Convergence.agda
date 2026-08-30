module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base


private
  oneℝ : Real.ℝ
  oneℝ = CommRingStr.1r (snd ℝCommRing)


GeometricPowersTendToZero : Real.ℝ → Type₀
GeometricPowersTendToZero x =
  isLimitSequence (geometricTerms x) zeroℝ


geometricAbsoluteTermsPath : ∀ x →
  (Abs.absℝ ∘ geometricTerms x) ≡
  geometricTerms (Abs.absℝ x)
geometricAbsoluteTermsPath x =
  funExt λ n → absPow n x


-- This identifies the native absolute Cauchy premise without choosing a
-- rate of convergence.  `Geometric.Comparison` now combines it with the
-- general absolute-convergence theorem and a rational majorant.

geometricSeriesIsAbsolutelyCauchy : ∀ x →
  IsCauchySeries (geometricTerms (Abs.absℝ x)) →
  IsAbsolutelyCauchySeries (geometricTerms x)
geometricSeriesIsAbsolutelyCauchy x absolute-powers-cauchy =
  subst IsCauchySeries
    (sym (geometricAbsoluteTermsPath x))
    absolute-powers-cauchy


geometricSeriesIsAbsolutelySummable : ∀ x →
  IsCauchySeries (geometricTerms (Abs.absℝ x)) →
  AbsolutelySummable (geometricTerms x)
geometricSeriesIsAbsolutelySummable x =
  absoluteCauchySeriesIsAbsolutelySummable (geometricTerms x)
  ∘ geometricSeriesIsAbsolutelyCauchy x


-- The algebraic finite-sum identity turns convergence of the powers into
-- convergence of the series.  No absolute-convergence detour is needed.

geometricSeriesHasSum : ∀ x →
  (x<one : x <ℝ oneℝ) →
  GeometricPowersTendToZero x →
  HasSum
    (geometricTerms x)
    (positiveReciprocal
      (oneℝ Group.- x)
      (strictlyPositiveDifference≪ x oneℝ x<one))
geometricSeriesHasSum x x<one powers-limit =
  eventuallyEqualPresIsLimitSequence
    ∣ 0 , (λ n _ →
      sym (geometricPartialSumByReciprocal
        x n positive-denominator)) ∣₁
    candidate-limit
  where
  positive-denominator : zeroℝ <ℝ oneℝ Group.- x
  positive-denominator =
    strictlyPositiveDifference≪ x oneℝ x<one

  reciprocal : Real.ℝ
  reciprocal =
    positiveReciprocal
      (oneℝ Group.- x) positive-denominator

  one-minus-powers : RealSequence
  one-minus-powers n = oneℝ Group.- x ^ⁿ n

  one-minus-powers-limit :
    isLimitSequence one-minus-powers oneℝ
  one-minus-powers-limit =
    subst (isLimitSequence one-minus-powers)
      (sub-zero-right oneℝ)
      (subPresIsLimitSequence
        (constantIsLimitSequence oneℝ)
        powers-limit)

  candidate : RealSequence
  candidate n = reciprocal Mul.· one-minus-powers n

  candidate-limit :
    isLimitSequence candidate reciprocal
  candidate-limit =
    subst (isLimitSequence candidate)
      (mul-one-right reciprocal)
      (mulPresIsLimitSequence
        (constantIsLimitSequence reciprocal)
        one-minus-powers-limit)


geometricSeriesSummable : ∀ x →
  x <ℝ oneℝ →
  GeometricPowersTendToZero x →
  Summable (geometricTerms x)
geometricSeriesSummable x x<one powers-limit =
  positiveReciprocal
    (oneℝ Group.- x)
    (strictlyPositiveDifference≪ x oneℝ x<one)
  , geometricSeriesHasSum x x<one powers-limit


geometricSeriesSummable→powersTendToZero : ∀ x →
  Summable (geometricTerms x) →
  GeometricPowersTendToZero x
geometricSeriesSummable→powersTendToZero x =
  summableTermsTendToZero (geometricTerms x)


-- At the native truncation strength, this is the exact convergence
-- criterion.  Both sides are propositions; the equivalence therefore does
-- not expose or select a convergence modulus.

geometricPowersTendToZero≃summable : ∀ x →
  x <ℝ oneℝ →
  GeometricPowersTendToZero x ≃
  Summable (geometricTerms x)
geometricPowersTendToZero≃summable x x<one =
  propBiimpl→Equiv
    (isPropIsLimitSequence (geometricTerms x) zeroℝ)
    (isPropSummable (geometricTerms x))
    (geometricSeriesSummable x x<one)
    (geometricSeriesSummable→powersTendToZero x)


geometricPowersTendToZero≃isCauchySeries : ∀ x →
  x <ℝ oneℝ →
  GeometricPowersTendToZero x ≃
  IsCauchySeries (geometricTerms x)
geometricPowersTendToZero≃isCauchySeries x x<one =
  propBiimpl→Equiv
    (isPropIsLimitSequence (geometricTerms x) zeroℝ)
    (isPropIsCauchySeries (geometricTerms x))
    (summableIsCauchySeries (geometricTerms x) ∘
      geometricSeriesSummable x x<one)
    (geometricSeriesSummable→powersTendToZero x ∘
      cauchySeriesIsSummable (geometricTerms x))


seriesSum-geometric : ∀ x →
  (x<one : x <ℝ oneℝ) →
  (powers-limit : GeometricPowersTendToZero x) →
  (summable : Summable (geometricTerms x)) →
  seriesSum (geometricTerms x) summable ≡
  positiveReciprocal
    (oneℝ Group.- x)
    (strictlyPositiveDifference≪ x oneℝ x<one)
seriesSum-geometric x x<one powers-limit summable =
  seriesSumIndependent
    (geometricTerms x)
    summable
    (geometricSeriesSummable x x<one powers-limit)

module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Geometric where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Convergence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Affine
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base


private
  oneℝ : Real.ℝ
  oneℝ = CommRingStr.1r (snd ℝCommRing)


unitCoefficients : RealSequence
unitCoefficients _ = oneℝ


powerSeriesTerms-unitCoefficients : ∀ x n →
  powerSeriesTerms unitCoefficients x n ≡
  geometricTerms x n
powerSeriesTerms-unitCoefficients x n =
  mul-one-left (x ^ⁿ n)


powerSeriesTerms-unitCoefficients-sequence : ∀ x →
  powerSeriesTerms unitCoefficients x ≡
  geometricTerms x
powerSeriesTerms-unitCoefficients-sequence x =
  funExt (powerSeriesTerms-unitCoefficients x)


unitPowerSeriesSummable : ∀ x →
  x <ℝ oneℝ →
  GeometricPowersTendToZero x →
  PowerSeriesSummableAt unitCoefficients x
unitPowerSeriesSummable x x<one powers-limit =
  subst Summable
    (sym (powerSeriesTerms-unitCoefficients-sequence x))
    (geometricSeriesSummable x x<one powers-limit)


powerSeriesValue-unitCoefficients : ∀ x →
  (x<one : x <ℝ oneℝ) →
  (powers-limit : GeometricPowersTendToZero x) →
  (summable : PowerSeriesSummableAt unitCoefficients x) →
  powerSeriesValue unitCoefficients x summable ≡
  geometricReciprocal x x<one
powerSeriesValue-unitCoefficients
    x x<one powers-limit summable =
  seriesSumIndependent
    (powerSeriesTerms unitCoefficients x)
    summable reciprocal-summable
  where
  reciprocal : Real.ℝ
  reciprocal = geometricReciprocal x x<one

  unit-has-sum :
    HasSum (powerSeriesTerms unitCoefficients x) reciprocal
  unit-has-sum =
    subst (λ terms → HasSum terms reciprocal)
      (sym (powerSeriesTerms-unitCoefficients-sequence x))
      (geometricSeriesHasSum x x<one powers-limit)

  reciprocal-summable :
    PowerSeriesSummableAt unitCoefficients x
  reciprocal-summable = reciprocal , unit-has-sum

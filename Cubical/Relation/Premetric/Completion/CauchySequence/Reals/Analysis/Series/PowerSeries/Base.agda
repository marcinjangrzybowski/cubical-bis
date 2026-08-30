module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (zero)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations


powerSeriesTerms :
  RealSequence → Real.ℝ → RealSequence
powerSeriesTerms coefficients x n =
  coefficients n Mul.· x ^ⁿ n


CoefficientAbsBound : ℚ₊ → RealSequence → Type₀
CoefficientAbsBound C coefficients =
  ∀ n →
  Abs.absℝ (coefficients n) ≤ℝ Real.ιℚ (fst C)


PowerSeriesSummableAt : RealSequence → Real.ℝ → Type₀
PowerSeriesSummableAt coefficients x =
  Summable (powerSeriesTerms coefficients x)


isPropPowerSeriesSummableAt : ∀ coefficients x →
  isProp (PowerSeriesSummableAt coefficients x)
isPropPowerSeriesSummableAt coefficients x =
  isPropSummable (powerSeriesTerms coefficients x)


powerSeriesValue : ∀ coefficients x →
  PowerSeriesSummableAt coefficients x → Real.ℝ
powerSeriesValue coefficients x summable =
  seriesSum (powerSeriesTerms coefficients x) summable


powerSeriesValueHasSum : ∀ coefficients x summable →
  HasSum
    (powerSeriesTerms coefficients x)
    (powerSeriesValue coefficients x summable)
powerSeriesValueHasSum coefficients x summable =
  seriesSumHasSum (powerSeriesTerms coefficients x) summable


powerSeriesTerms-zero : ∀ coefficients →
  powerSeriesTerms coefficients zeroℝ zero ≡
  coefficients zero
powerSeriesTerms-zero coefficients =
  mul-one-right (coefficients zero)


powerSeriesTerms-add : ∀ a b x n →
  powerSeriesTerms (λ k → a k Add.+ b k) x n ≡
  powerSeriesTerms a x n Add.+ powerSeriesTerms b x n
powerSeriesTerms-add a b x n =
  mul-distrib-over-add-left (a n) (b n) (x ^ⁿ n)


powerSeriesTerms-scale : ∀ c coefficients x n →
  powerSeriesTerms (scaleSeries c coefficients) x n ≡
  scaleSeries c (powerSeriesTerms coefficients x) n
powerSeriesTerms-scale c coefficients x n =
  sym (mul-assoc c (coefficients n) (x ^ⁿ n))

module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.LowerBound where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Order
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential


-- The first two series terms give the sharp elementary lower bound
-- 1 + x ≤ exp(x) on the nonnegative half-line.  Unlike a mere example,
-- this bound is the analytic input that turns the addition law into strict
-- monotonicity.

exponentialCoefficient-one :
  exponentialCoefficients (suc zero) ≡ Real.ιℚ 1
exponentialCoefficient-one =
    sym (mul-one-left (exponentialCoefficients (suc zero)))
  ∙ cong (Mul._· exponentialCoefficients (suc zero))
      (sym realNatural-one)
  ∙ exponentialCoefficient-suc zero
  ∙ exponentialCoefficient-zero


exponentialPowerSeriesTerm-zero : ∀ x →
  powerSeriesTerms exponentialCoefficients x zero ≡ Real.ιℚ 1
exponentialPowerSeriesTerm-zero x =
    mul-one-right (exponentialCoefficients zero)
  ∙ exponentialCoefficient-zero


exponentialPowerSeriesTerm-one : ∀ x →
  powerSeriesTerms exponentialCoefficients x (suc zero) ≡ x
exponentialPowerSeriesTerm-one x =
    cong₂ Mul._·_
      exponentialCoefficient-one
      (ℝExponentiation.x^1≡x x)
  ∙ mul-one-left x


exponentialPartialSum-two : ∀ x →
  partialSum (powerSeriesTerms exponentialCoefficients x)
      (suc (suc zero))
    ≡ Real.ιℚ 1 Add.+ x
exponentialPartialSum-two x =
    cong
      (Add._+ powerSeriesTerms exponentialCoefficients x (suc zero))
      (add-zero-left
        (powerSeriesTerms exponentialCoefficients x zero))
  ∙ cong₂ Add._+_
      (exponentialPowerSeriesTerm-zero x)
      (exponentialPowerSeriesTerm-one x)


one-plus-self≤expℝOfNonnegative : ∀ x →
  zeroℝ ≤ℝ x → Real.ιℚ 1 Add.+ x ≤ℝ expℝ x
one-plus-self≤expℝOfNonnegative x 0≤x =
  subst
    (_≤ℝ expℝ x)
    (exponentialPartialSum-two x)
    (partialSumLeSeriesSum terms summable nonnegative
      (suc (suc zero)))
  where
  terms : RealSequence
  terms = powerSeriesTerms exponentialCoefficients x

  summable : Summable terms
  summable = exponentialPowerSeriesIsSummable x

  nonnegative : ∀ n → zeroℝ ≤ℝ terms n
  nonnegative = exponentialPowerSeriesTerm-nonnegativeAt x 0≤x


one<expℝOfPositive : ∀ x →
  zeroℝ <ℝ x → Real.ιℚ 1 <ℝ expℝ x
one<expℝOfPositive x 0<x =
  ≪≤ℝ-trans (Real.ιℚ 1) (Real.ιℚ 1 Add.+ x) (expℝ x)
    (subst (_<ℝ Real.ιℚ 1 Add.+ x)
      (add-zero-right (Real.ιℚ 1))
      (<ℝ-add-left zeroℝ x (Real.ιℚ 1) 0<x))
    (one-plus-self≤expℝOfNonnegative x
      (<ℝ-weaken zeroℝ x 0<x))

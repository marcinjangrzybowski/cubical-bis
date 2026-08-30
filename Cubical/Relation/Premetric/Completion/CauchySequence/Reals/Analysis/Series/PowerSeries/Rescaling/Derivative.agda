module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Rescaling.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Rationals.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Basic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Chain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Rescaling


-- Formal differentiation commutes with linear substitution up to the
-- expected chain-rule scalar.  This statement is coefficient-level and
-- therefore remains useful for finite series and radius-restricted series.

formalDerivative-rescaleCoefficients : ∀ c coefficients →
  formalDerivative (rescaleCoefficients c coefficients)
    ≡
  scaleSeries c
    (rescaleCoefficients c (formalDerivative coefficients))
formalDerivative-rescaleCoefficients c coefficients =
  funExt λ n →
      mul-assoc
        (realNatural (suc n)) (coefficients (suc n))
        (c Mul.· c ^ⁿ n)
    ∙ mul-assoc
        (realNatural (suc n) Mul.· coefficients (suc n))
        c (c ^ⁿ n)
    ∙ cong
        (Mul._· c ^ⁿ n)
        (mul-comm
          (realNatural (suc n) Mul.· coefficients (suc n)) c)
    ∙ sym
        (mul-assoc c
          (realNatural (suc n) Mul.· coefficients (suc n))
          (c ^ⁿ n))


formalDerivativeRescaleLocallyUniform : ∀ c coefficients →
  LocallyUniformPowerSeries (formalDerivative coefficients) →
  LocallyUniformPowerSeries
    (formalDerivative (rescaleCoefficients c coefficients))
formalDerivativeRescaleLocallyUniform c coefficients derivative-local =
  subst LocallyUniformPowerSeries
    (sym (formalDerivative-rescaleCoefficients c coefficients))
    (scaleLocallyUniformPowerSeries c
      (rescaleCoefficients c (formalDerivative coefficients))
      (rescaleLocallyUniformPowerSeries c
        (formalDerivative coefficients) derivative-local))


-- The input scaling itself has its exact constant derivative.  Deriving it
-- from the general scalar rule retains all quantitative completion proofs.

linearRescalingHasDerivative : ∀ c →
  IsDerivative
    (λ x → c Mul.· x)
    (λ _ → c)
linearRescalingHasDerivative c =
  subst
    (IsDerivative (λ x → c Mul.· x))
    (funExt λ _ → mul-one-right c)
    (scaleHasDerivative
      (idfun Real.ℝ) (λ _ → Real.ιℚ 1) c
      identityHasDerivative)


-- Analytic rescaling theorem.  It is deliberately phrased using the
-- derivative of the original series at c·x: clients do not need to unfold
-- the transported convergence proof for the formally rescaled derivative.

locallyUniformPowerSeriesRescaleHasDerivative : ∀ c coefficients
  (local : LocallyUniformPowerSeries coefficients)
  (derivative-local :
    LocallyUniformPowerSeries (formalDerivative coefficients)) →
  LocallyUniformPowerSeriesDifferenceFactor coefficients →
  IsDerivative
    (locallyUniformPowerSeriesValue
      (rescaleCoefficients c coefficients)
      (rescaleLocallyUniformPowerSeries c coefficients local))
    (λ x →
      locallyUniformPowerSeriesValue
        (formalDerivative coefficients) derivative-local
        (c Mul.· x)
      Mul.· c)
locallyUniformPowerSeriesRescaleHasDerivative
  c coefficients local derivative-local factor-local =
  subst
    (λ function → IsDerivative function rescaled-derivative)
    (sym rescaled-function-path)
    composed-has-derivative
  where
  original-function : Real.ℝ → Real.ℝ
  original-function =
    locallyUniformPowerSeriesValue coefficients local

  original-derivative : Real.ℝ → Real.ℝ
  original-derivative =
    locallyUniformPowerSeriesValue
      (formalDerivative coefficients) derivative-local

  rescaled-function : Real.ℝ → Real.ℝ
  rescaled-function =
    locallyUniformPowerSeriesValue
      (rescaleCoefficients c coefficients)
      (rescaleLocallyUniformPowerSeries c coefficients local)

  rescaled-derivative : Real.ℝ → Real.ℝ
  rescaled-derivative x =
    original-derivative (c Mul.· x) Mul.· c

  composed-has-derivative :
    IsDerivative
      (λ x → original-function (c Mul.· x))
      rescaled-derivative
  composed-has-derivative =
    chainHasDerivative
      (λ x → c Mul.· x) (λ _ → c)
      original-function original-derivative
      (linearRescalingHasDerivative c)
      (locallyUniformPowerSeriesHasFormalDerivative
        coefficients local derivative-local factor-local)

  rescaled-function-path :
    rescaled-function ≡
    (λ x → original-function (c Mul.· x))
  rescaled-function-path =
    funExt
      (locallyUniformPowerSeriesValue-rescale
        c coefficients local
        (rescaleLocallyUniformPowerSeries c coefficients local))


-- The transported formal-derivative evaluator agrees with the chain-rule
-- expression.  The proof goes through specified sums, so it never unfolds
-- the opaque whole-line evaluator or its Archimedean convergence witness.

locallyUniformPowerSeriesFormalDerivativeRescaleValue : ∀
  c coefficients
  (derivative-local :
    LocallyUniformPowerSeries (formalDerivative coefficients))
  x →
  locallyUniformPowerSeriesValue
      (formalDerivative (rescaleCoefficients c coefficients))
      (formalDerivativeRescaleLocallyUniform
        c coefficients derivative-local) x
    ≡
  locallyUniformPowerSeriesValue
      (formalDerivative coefficients) derivative-local
      (c Mul.· x)
    Mul.· c
locallyUniformPowerSeriesFormalDerivativeRescaleValue
  c coefficients derivative-local x =
  seriesSumIndependent formal-terms target-summable expected-summable
  where
  derivative-coefficients : RealSequence
  derivative-coefficients = formalDerivative coefficients

  rescaled-derivative-coefficients : RealSequence
  rescaled-derivative-coefficients =
    rescaleCoefficients c derivative-coefficients

  formal-terms : RealSequence
  formal-terms =
    powerSeriesTerms
      (formalDerivative (rescaleCoefficients c coefficients)) x

  derivative-value : Real.ℝ
  derivative-value =
    locallyUniformPowerSeriesValue
      derivative-coefficients derivative-local (c Mul.· x)

  target-summable : Summable formal-terms
  target-summable =
    locallyUniformPowerSeriesValue
        (formalDerivative (rescaleCoefficients c coefficients))
        (formalDerivativeRescaleLocallyUniform
          c coefficients derivative-local) x
    , locallyUniformPowerSeriesValueHasSum
        (formalDerivative (rescaleCoefficients c coefficients))
        (formalDerivativeRescaleLocallyUniform
          c coefficients derivative-local) x

  derivative-has-sum :
    HasSum
      (powerSeriesTerms derivative-coefficients (c Mul.· x))
      derivative-value
  derivative-has-sum =
    locallyUniformPowerSeriesValueHasSum
      derivative-coefficients derivative-local (c Mul.· x)

  rescaled-derivative-has-sum :
    HasSum
      (powerSeriesTerms rescaled-derivative-coefficients x)
      derivative-value
  rescaled-derivative-has-sum =
    rescalePowerSeriesHasSum
      c derivative-coefficients x derivative-value derivative-has-sum

  scaled-terms-have-left-product :
    HasSum
      (scaleSeries c
        (powerSeriesTerms rescaled-derivative-coefficients x))
      (c Mul.· derivative-value)
  scaled-terms-have-left-product =
    scaleHasSum c
      (powerSeriesTerms rescaled-derivative-coefficients x)
      derivative-value rescaled-derivative-has-sum

  scaled-coefficient-terms-have-left-product :
    HasSum
      (powerSeriesTerms
        (scaleSeries c rescaled-derivative-coefficients) x)
      (c Mul.· derivative-value)
  scaled-coefficient-terms-have-left-product =
    subst (λ terms → HasSum terms (c Mul.· derivative-value))
      (sym
        (powerSeriesTerms-scale-sequence
          c rescaled-derivative-coefficients x))
      scaled-terms-have-left-product

  formal-terms-have-left-product :
    HasSum formal-terms (c Mul.· derivative-value)
  formal-terms-have-left-product =
    subst (λ terms → HasSum terms (c Mul.· derivative-value))
      (sym
        (cong (λ sequence → powerSeriesTerms sequence x)
          (formalDerivative-rescaleCoefficients c coefficients)))
      scaled-coefficient-terms-have-left-product

  formal-terms-have-right-product :
    HasSum formal-terms (derivative-value Mul.· c)
  formal-terms-have-right-product =
    subst (HasSum formal-terms)
      (mul-comm c derivative-value)
      formal-terms-have-left-product

  expected-summable : Summable formal-terms
  expected-summable =
    derivative-value Mul.· c
    , formal-terms-have-right-product


-- Fully normalized result: the constructed rescaled series differentiates
-- to its own formal derivative, not merely to an extensionally equal chain-
-- rule function.

locallyUniformPowerSeriesRescaleHasFormalDerivative : ∀ c coefficients
  (local : LocallyUniformPowerSeries coefficients)
  (derivative-local :
    LocallyUniformPowerSeries (formalDerivative coefficients)) →
  LocallyUniformPowerSeriesDifferenceFactor coefficients →
  IsDerivative
    (locallyUniformPowerSeriesValue
      (rescaleCoefficients c coefficients)
      (rescaleLocallyUniformPowerSeries c coefficients local))
    (locallyUniformPowerSeriesValue
      (formalDerivative (rescaleCoefficients c coefficients))
      (formalDerivativeRescaleLocallyUniform
        c coefficients derivative-local))
locallyUniformPowerSeriesRescaleHasFormalDerivative
  c coefficients local derivative-local factor-local =
  subst
    (IsDerivative rescaled-function)
    (sym derivative-function-path)
    (locallyUniformPowerSeriesRescaleHasDerivative
      c coefficients local derivative-local factor-local)
  where
  rescaled-function : Real.ℝ → Real.ℝ
  rescaled-function =
    locallyUniformPowerSeriesValue
      (rescaleCoefficients c coefficients)
      (rescaleLocallyUniformPowerSeries c coefficients local)

  derivative-function-path :
    locallyUniformPowerSeriesValue
      (formalDerivative (rescaleCoefficients c coefficients))
      (formalDerivativeRescaleLocallyUniform
        c coefficients derivative-local)
    ≡
    (λ x →
      locallyUniformPowerSeriesValue
        (formalDerivative coefficients) derivative-local
        (c Mul.· x)
      Mul.· c)
  derivative-function-path =
    funExt
      (locallyUniformPowerSeriesFormalDerivativeRescaleValue
        c coefficients derivative-local)

module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Power where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Basic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Chain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference


private
  realPairPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
  realPairPremetricSpace =
    PremetricProduct Real.ℝPremetricSpace Real.ℝPremetricSpace

  pairLeftIsContinuous :
    isContinuous
      (snd realPairPremetricSpace)
      fst
      (snd Real.ℝPremetricSpace)
  pairLeftIsContinuous =
    snd
      (productFstC
        {M = Real.ℝPremetricSpace}
        {N = Real.ℝPremetricSpace})

  pairRightIsContinuous :
    isContinuous
      (snd realPairPremetricSpace)
      snd
      (snd Real.ℝPremetricSpace)
  pairRightIsContinuous =
    snd
      (productSndC
        {M = Real.ℝPremetricSpace}
        {N = Real.ℝPremetricSpace})


zeroPowerHasDerivative :
  IsDerivative
    (λ x → x ^ⁿ zero)
    (λ _ → Real.ιℚ 0)
zeroPowerHasDerivative =
  constantHasDerivative (Real.ιℚ 1)


successorPowerHasDerivative :
  ∀ n →
  IsDerivative
    (λ x → x ^ⁿ suc n)
    (λ x → realNatural (suc n) Mul.· x ^ⁿ n)
successorPowerHasDerivative n =
  continuousDifferenceFactorGivesDerivative
    (snd Real.ℝPremetricSpace)
    (λ x → x)
    (λ x → x ^ⁿ suc n)
    (λ x → realNatural (suc n) Mul.· x ^ⁿ n)
    (λ point →
      powerDifferenceFactor (fst point) (snd point) n)
    (λ x y → powerDifferenceFactor-identity x y n)
    (λ x → powerDifferenceFactor-diagonal x n)
    (powerDifferenceFactorOfContinuousIsContinuous
      (snd realPairPremetricSpace)
      fst snd
      pairLeftIsContinuous pairRightIsContinuous n)


naturalPowerDerivative : ℕ → Real.ℝ → Real.ℝ
naturalPowerDerivative zero x = Real.ιℚ 0
naturalPowerDerivative (suc n) x =
  realNatural (suc n) Mul.· x ^ⁿ n


naturalPowerHasDerivative : ∀ n →
  IsDerivative
    (λ x → x ^ⁿ n)
    (naturalPowerDerivative n)
naturalPowerHasDerivative zero = zeroPowerHasDerivative
naturalPowerHasDerivative (suc n) = successorPowerHasDerivative n


naturalPowerCompositionHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → Real.ℝ) →
  isContinuous source coordinate
    (snd Real.ℝPremetricSpace) →
  IsDerivativeAlong source coordinate function derivative →
  ∀ n →
  IsDerivativeAlong
    source coordinate
    (λ point → function point ^ⁿ n)
    (λ point →
      naturalPowerDerivative n (function point) Mul.·
        derivative point)
naturalPowerCompositionHasDerivativeAlong
  source coordinate function derivative
  coordinate-continuous function-derivative n =
    chainHasDerivativeAlong
      source coordinate function derivative
      (λ x → x ^ⁿ n)
      (naturalPowerDerivative n)
      coordinate-continuous function-derivative
      (naturalPowerHasDerivative n)


naturalPowerCompositionHasDerivative :
  ∀ function derivative →
  IsDerivative function derivative →
  ∀ n →
  IsDerivative
    (λ x → function x ^ⁿ n)
    (λ x →
      naturalPowerDerivative n (function x) Mul.· derivative x)
naturalPowerCompositionHasDerivative
  function derivative function-derivative n =
    chainHasDerivative
      function derivative
      (λ x → x ^ⁿ n)
      (naturalPowerDerivative n)
      function-derivative
      (naturalPowerHasDerivative n)

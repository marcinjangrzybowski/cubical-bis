module Cubical.HITs.CauchyRealsP.Analysis.Derivative.Power where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Basic
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

private
  realPairPremetricSpace :
    PremetricSpace ℓ-zero ℓ-zero
  realPairPremetricSpace =
    PremetricProduct
      ℝPremetricSpace ℝPremetricSpace

  pairLeftIsContinuous :
    isContinuous
      (snd realPairPremetricSpace)
      fst
      (snd ℝPremetricSpace)
  pairLeftIsContinuous =
    snd
      (productFstC
        {M = ℝPremetricSpace}
        {N = ℝPremetricSpace})

  pairRightIsContinuous :
    isContinuous
      (snd realPairPremetricSpace)
      snd
      (snd ℝPremetricSpace)
  pairRightIsContinuous =
    snd
      (productSndC
        {M = ℝPremetricSpace}
        {N = ℝPremetricSpace})

zeroPowerHasDerivative :
  IsDerivative
    (λ x → x ^ⁿ zero)
    (λ _ → 0)
zeroPowerHasDerivative =
  constantHasDerivative 1

successorPowerHasDerivative :
  ∀ n →
  IsDerivative
    (λ x → x ^ⁿ suc n)
    (λ x →
      realNatural (suc n) · x ^ⁿ n)
successorPowerHasDerivative n =
  continuousDifferenceFactorGivesDerivative
    (snd ℝPremetricSpace)
    (λ x → x)
    (λ x → x ^ⁿ suc n)
    (λ x →
      realNatural (suc n) · x ^ⁿ n)
    (λ point →
      powerDifferenceFactor
        (fst point) (snd point) n)
    (λ x y →
      powerDifferenceFactor-identity x y n)
    (λ x →
      powerDifferenceFactor-diagonal x n)
    (powerDifferenceFactorOfContinuousIsContinuous
      (snd realPairPremetricSpace)
      fst snd
      pairLeftIsContinuous
      pairRightIsContinuous n)

naturalPowerDerivative : ℕ → ℝ → ℝ
naturalPowerDerivative zero x =
  0
naturalPowerDerivative (suc n) x =
  realNatural (suc n) · x ^ⁿ n

naturalPowerHasDerivative : ∀ n →
  IsDerivative
    (λ x → x ^ⁿ n)
    (naturalPowerDerivative n)
naturalPowerHasDerivative zero =
  zeroPowerHasDerivative
naturalPowerHasDerivative (suc n) =
  successorPowerHasDerivative n

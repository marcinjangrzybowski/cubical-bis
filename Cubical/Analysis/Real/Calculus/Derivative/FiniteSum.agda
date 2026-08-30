module Cubical.Analysis.Real.Calculus.Derivative.FiniteSum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.FinData using (FinVec)
import Cubical.Data.FinData as FD

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps

open import Cubical.Relation.Premetric.Base

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Basic
open import Cubical.Analysis.Real.Calculus.Derivative.Algebra


private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)

open ℝSum using (∑)


finiteSumHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ} {n}
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ)
    (function derivative : FinVec (A → ℝ) n) →
  (∀ i →
    IsDerivativeAlong
      source coordinate (function i) (derivative i)) →
  IsDerivativeAlong
    source coordinate
    (λ point → ∑ (λ i → function i point))
    (λ point → ∑ (λ i → derivative i point))
finiteSumHasDerivativeAlong {n = zero}
  source coordinate function derivative has-derivative =
    constantHasDerivativeAlong source coordinate 0ℝ
finiteSumHasDerivativeAlong {n = suc n}
  source coordinate function derivative has-derivative =
    addHasDerivativeAlong
      source coordinate
      (function FD.zero)
      (λ point →
        ∑ (λ i → function (FD.suc i) point))
      (derivative FD.zero)
      (λ point →
        ∑ (λ i → derivative (FD.suc i) point))
      (has-derivative FD.zero)
      (finiteSumHasDerivativeAlong
        source coordinate
        (function ∘ FD.suc)
        (derivative ∘ FD.suc)
        (has-derivative ∘ FD.suc))


finiteSumHasDerivative :
  ∀ {n}
    (function derivative : FinVec (ℝ → ℝ) n) →
  (∀ i → IsDerivative (function i) (derivative i)) →
  IsDerivative
    (λ x → ∑ (λ i → function i x))
    (λ x → ∑ (λ i → derivative i x))
finiteSumHasDerivative function derivative =
  finiteSumHasDerivativeAlong
    (ℝPremetricSpace .snd) (idfun ℝ)
    function derivative

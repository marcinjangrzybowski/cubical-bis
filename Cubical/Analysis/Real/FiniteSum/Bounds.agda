module Cubical.Analysis.Real.FiniteSum.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (FinVec)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
import Cubical.Algebra.OrderedCommRing.Properties as OrderedProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Structure


private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)
  module ℝSumOrder =
    OrderedProperties.SumTheory ℝOrderedCommRing

open ℝSum using (∑)


finiteSumMono : ∀ {n} (x y : FinVec ℝ n) →
  (∀ i → x i ≤ℝ y i) → ∑ x ≤ℝ ∑ y
finiteSumMono = ℝSumOrder.∑Mono≤


finiteSumAbsBound : ∀ {n} (x : FinVec ℝ n) →
  absℝ (∑ x) ≤ℝ ∑ (absℝ ∘ x)
finiteSumAbsBound x =
  subst2 _≤ℝ_
    (sym (absAsMax (∑ x)))
    (sym (ℝSum.∑Ext (absAsMax ∘ x)))
    (ℝSumOrder.abs∑≤∑absFinVec x)

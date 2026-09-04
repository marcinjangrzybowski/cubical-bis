module Cubical.Analysis.Real.FiniteSum.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (FinVec)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
import Cubical.Algebra.OrderedCommRing.Properties as OrderedProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Structure
open import Cubical.Analysis.Real.FiniteSum.Algebra


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


finiteSumAbsBoundBy : ∀ {n} (x bounds : FinVec ℝ n) →
  (∀ i → absℝ (x i) ≤ℝ bounds i) → absℝ (∑ x) ≤ℝ ∑ bounds
finiteSumAbsBoundBy x bounds pointwise =
  ≤ℝ-trans (absℝ (∑ x)) (∑ (absℝ ∘ x)) (∑ bounds)
    (finiteSumAbsBound x)
    (finiteSumMono (absℝ ∘ x) bounds pointwise)


-- Nonnegative weights turn a common absolute bound into a bound scaled
-- by the total weight.  Riemann sums use the cell widths as weights.
finiteSumWeightedAbsBound : ∀ {n} (weights x : FinVec ℝ n) bound →
  (∀ i → 0ℝ ≤ℝ weights i) →
  (∀ i → absℝ (x i) ≤ℝ bound) →
  absℝ (∑ (λ i → weights i · x i)) ≤ℝ (∑ weights) · bound
finiteSumWeightedAbsBound weights x bound nonnegative pointwise =
  subst (absℝ (∑ (λ i → weights i · x i)) ≤ℝ_)
    (sym (finiteSumMulRight bound weights))
    (finiteSumAbsBoundBy
      (λ i → weights i · x i) (λ i → weights i · bound)
      (λ i →
        subst (_≤ℝ weights i · bound)
          (sym
            (absMul (weights i) (x i)
            ∙ cong (_· absℝ (x i))
                (absOfNonnegative (weights i) (nonnegative i))))
          (mulPres≤L (absℝ (x i)) bound (weights i)
            (0≤→isNonnegative (weights i) (nonnegative i))
            (pointwise i))))

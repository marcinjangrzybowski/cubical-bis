module Cubical.Analysis.Real.Calculus.MeanValue.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.FinData using (FinVec)
import Cubical.Data.FinData as FD
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Relation.Premetric.Base

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.FiniteSum.Algebra
open import Cubical.Analysis.Real.FiniteSum.Bounds
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Calculus.Derivative.Base


private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)

open ℝSum using (∑)


-- This is the uniform remainder estimate used by the constructive
-- partition proof of the mean-value inequality.  The radius remains
-- propositionally truncated: no global modulus is selected.

IsRadiuswiseUniformDerivative :
  (function derivative : ℝ → ℝ) → Type₀
IsRadiuswiseUniformDerivative function derivative =
  ∀ ε →
    ∃[ δ ∈ ℚ₊ ]
      (∀ x y →
        x ∼[ δ ] y →
        absℝ
            ((function y - function x) -
              derivative x · (y - x))
          ≤ℝ
        rat (fst ε) · absℝ (y - x))


isPropIsRadiuswiseUniformDerivative : ∀ function derivative →
  isProp (IsRadiuswiseUniformDerivative function derivative)
isPropIsRadiuswiseUniformDerivative function derivative =
  isPropΠ λ _ → squash₁


radiuswiseUniformDerivative→derivative : ∀ function derivative →
  IsRadiuswiseUniformDerivative function derivative →
  IsDerivative function derivative
radiuswiseUniformDerivative→derivative
  function derivative uniformly-differentiable x ε =
  PT.map
    (λ { (δ , bound) →
      δ , λ y x∼y → bound x y x∼y })
    (uniformly-differentiable ε)


private
  derivativeErrorReconstructsDifference : ∀ function derivative x y →
    ((function y - function x) - derivative x · (y - x)) +
        derivative x · (y - x)
      ≡
    function y - function x
  derivativeErrorReconstructsDifference function derivative x y =
    sym (addAssoc
      (function y - function x)
      (- (derivative x · (y - x)))
      (derivative x · (y - x)))
    ∙ cong ((function y - function x) +_)
        (addInvL (derivative x · (y - x)))
    ∙ addIdR (function y - function x)


-- A fine partition turns the uniform first-order estimate into a global
-- endpoint bound.  This is the telescoping core of the mean-value
-- inequality and is independent of any integration existence theorem.

uniformDerivativePartitionBound : ∀ function derivative ε δ →
  (∀ x y →
    x ∼[ δ ] y →
    absℝ
        ((function y - function x) -
          derivative x · (y - x))
      ≤ℝ
    rat (fst ε) · absℝ (y - x)) →
  ∀ {a b} (partition : Partition[ a , b ]) →
  HasMeshBelow partition δ →
  ∀ bound →
  0ℝ ≤ℝ bound →
  (∀ x → absℝ (derivative x) ≤ℝ bound) →
  absℝ (function b - function a) ≤ℝ
    (rat (fst ε) + bound) · (b - a)
uniformDerivativePartitionBound
  function derivative ε δ remainder-bound
  {a} {b} partition mesh bound 0≤bound derivative-bound =
  subst2 _≤ℝ_
    (cong absℝ endpoint-difference-path)
    total-bound-path
    ( ≤ℝ-trans
      (absℝ (∑ differences))
      (∑ (absℝ ∘ differences))
      (∑ bounds)
      (finiteSumAbsBound differences)
      (finiteSumMono (absℝ ∘ differences) bounds term-bound))
  where
  open Partition partition

  differences : FinVec ℝ intervalCount
  differences i =
    function (points (FD.suc i)) -
    function (points (FD.weakenFin i))

  bounds : FinVec ℝ intervalCount
  bounds i = (rat (fst ε) + bound) · width partition i

  point-close : ∀ i →
    points (FD.weakenFin i) ∼[ δ ] points (FD.suc i)
  point-close i =
    absDifference<→closeness
      (points (FD.weakenFin i)) (points (FD.suc i)) δ
      (subst (_<ℝ rat (fst δ))
        (sym
          (absSubComm
            (points (FD.weakenFin i)) (points (FD.suc i))
          ∙ absOfNonnegative
              (width partition i) (width-nonnegative partition i)))
        (mesh i))

  linear-bound : ∀ i →
    absℝ
      (derivative (points (FD.weakenFin i)) · width partition i)
      ≤ℝ
    bound · width partition i
  linear-bound i =
    subst (_≤ℝ bound · width partition i)
      (sym
        (absMul
          (derivative (points (FD.weakenFin i)))
          (width partition i)
        ∙ cong
            (absℝ (derivative (points (FD.weakenFin i))) ·_)
            (absOfNonnegative
              (width partition i) (width-nonnegative partition i))))
      (mulPres≤R-0≤
        (absℝ (derivative (points (FD.weakenFin i))))
        bound (width partition i)
        (width-nonnegative partition i)
        (derivative-bound (points (FD.weakenFin i))))

  term-bound : ∀ i → absℝ (differences i) ≤ℝ bounds i
  term-bound i =
    subst2 _≤ℝ_
      (cong absℝ
        (sym
          (derivativeErrorReconstructsDifference
            function derivative
            (points (FD.weakenFin i))
            (points (FD.suc i)))))
      (sym
        (mulDistL (rat (fst ε)) bound (width partition i)))
      (≤ℝ-trans
        (absℝ
          (((differences i) -
              derivative (points (FD.weakenFin i)) · width partition i)
            + derivative (points (FD.weakenFin i)) · width partition i))
        (absℝ
            ((differences i) -
              derivative (points (FD.weakenFin i)) · width partition i)
          + absℝ
              (derivative (points (FD.weakenFin i)) · width partition i))
        (rat (fst ε) · width partition i +
          bound · width partition i)
        (absTriangle
          ((differences i) -
            derivative (points (FD.weakenFin i)) · width partition i)
          (derivative (points (FD.weakenFin i)) · width partition i))
        (addPres≤
          (absℝ
            ((differences i) -
              derivative (points (FD.weakenFin i)) · width partition i))
          (rat (fst ε) · width partition i)
          (absℝ
            (derivative (points (FD.weakenFin i)) · width partition i))
          (bound · width partition i)
          (subst
            (absℝ
                ((differences i) -
                  derivative (points (FD.weakenFin i)) · width partition i)
              ≤ℝ_)
            (cong (rat (fst ε) ·_)
              (absOfNonnegative
                (width partition i) (width-nonnegative partition i)))
            (remainder-bound
              (points (FD.weakenFin i))
              (points (FD.suc i))
              (point-close i)))
          (linear-bound i)))

  endpoint-difference-path : ∑ differences ≡ function b - function a
  endpoint-difference-path =
    finiteSumTelescoping (function ∘ points)
    ∙ cong₂ _-_
        (cong function rightEndpoint)
        (cong function leftEndpoint)

  total-bound-path : ∑ bounds ≡
    (rat (fst ε) + bound) · (b - a)
  total-bound-path =
    sym (finiteSumMulLeft
      (rat (fst ε) + bound) (width partition))
    ∙ cong ((rat (fst ε) + bound) ·_)
        (totalWidth partition)

module Cubical.Analysis.Real.Calculus.MeanValue.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.FinData using (FinVec)
import Cubical.Data.FinData as FD
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; 1₊; _·₊_)

open import Cubical.Relation.Premetric.Base

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
  using (subAddCancel)
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
open import Cubical.Analysis.Real.Order.Sequence
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Geometric.Rational
  using (two₊; halfℚ)
open import Cubical.Analysis.Real.FiniteSum.Algebra
open import Cubical.Analysis.Real.FiniteSum.Bounds
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Order
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic
  using (dyadicReal; dyadicRealIsLimitZero)
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
  using (fineTaggedPartition)
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
  ∀ (ε : ℚ₊) →
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


-- The interval-local version asks about neither derivative values nor
-- remainders outside the domain of the endpoint estimate.
IsRadiuswiseUniformDerivativeOn :
  (function derivative : ℝ → ℝ) → ℝ → ℝ → Type₀
IsRadiuswiseUniformDerivativeOn function derivative a b =
  ∀ (ε : ℚ₊) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ x y →
        a ≤ℝ x → x ≤ℝ b → a ≤ℝ y → y ≤ℝ b →
        x ∼[ δ ] y →
        absℝ ((function y - function x) - derivative x · (y - x))
          ≤ℝ rat (fst ε) · absℝ (y - x))

isPropIsRadiuswiseUniformDerivativeOn : ∀ function derivative a b →
  isProp (IsRadiuswiseUniformDerivativeOn function derivative a b)
isPropIsRadiuswiseUniformDerivativeOn function derivative a b =
  isPropΠ λ _ → squash₁

radiuswiseUniformDerivative→onInterval : ∀ function derivative a b →
  IsRadiuswiseUniformDerivative function derivative →
  IsRadiuswiseUniformDerivativeOn function derivative a b
radiuswiseUniformDerivative→onInterval
    function derivative a b uniformly-differentiable ε =
  PT.map (λ { (δ , bound) →
    δ , λ x y _ _ _ _ → bound x y })
    (uniformly-differentiable ε)

radiuswiseUniformDerivativeOn→subinterval :
  ∀ function derivative a b left right →
  a ≤ℝ left → right ≤ℝ b →
  IsRadiuswiseUniformDerivativeOn function derivative a b →
  IsRadiuswiseUniformDerivativeOn function derivative left right
radiuswiseUniformDerivativeOn→subinterval
    function derivative a b left right a≤left right≤b
    uniformly-differentiable ε =
  PT.map (λ { (δ , bound) →
    δ , λ x y left≤x x≤right left≤y y≤right →
      bound x y
        (≤ℝ-trans a left x a≤left left≤x)
        (≤ℝ-trans x right b x≤right right≤b)
        (≤ℝ-trans a left y a≤left left≤y)
        (≤ℝ-trans y right b y≤right right≤b) })
    (uniformly-differentiable ε)


private
  -- Bound a difference by its linear part and its remainder before
  -- substituting the partition-dependent expressions.
  differenceBoundFromRemainder : ∀ difference linear errorBound linearBound →
    absℝ (difference - linear) ≤ℝ errorBound →
    absℝ linear ≤ℝ linearBound →
    absℝ difference ≤ℝ errorBound + linearBound
  differenceBoundFromRemainder difference linear errorBound linearBound
      error≤bound linear≤bound =
    subst (_≤ℝ errorBound + linearBound)
      (cong absℝ (subAddCancel difference linear))
      (≤ℝ-trans
        (absℝ ((difference - linear) + linear))
        (absℝ (difference - linear) + absℝ linear)
        (errorBound + linearBound)
        (absTriangle (difference - linear) linear)
        (addPres≤
          (absℝ (difference - linear)) errorBound
          (absℝ linear) linearBound error≤bound linear≤bound))


-- A fine partition turns the uniform first-order estimate into a global
-- endpoint bound.  This is the telescoping core of the mean-value
-- inequality and is independent of any integration existence theorem.

uniformDerivativePartitionBoundAtPoints :
  ∀ (function derivative : ℝ → ℝ) (ε δ : ℚ₊) →
  ∀ {a b} (partition : Partition[ a , b ]) →
  (∀ i →
    let x = Partition.points partition (FD.weakenFin i)
        y = Partition.points partition (FD.suc i)
    in x ∼[ δ ] y →
    absℝ
        ((function y - function x) -
          derivative x · (y - x))
      ≤ℝ
    rat (fst ε) · absℝ (y - x)) →
  HasMeshBelow partition δ →
  ∀ bound →
  (∀ i →
    absℝ (derivative (Partition.points partition (FD.weakenFin i)))
      ≤ℝ bound) →
  absℝ (function b - function a) ≤ℝ
    (rat (fst ε) + bound) · (b - a)
uniformDerivativePartitionBoundAtPoints
  function derivative ε δ {a} {b} partition remainder-bound
  mesh bound derivative-bound =
  subst2 _≤ℝ_
    (cong absℝ endpoint-difference-path)
    total-bound-path
    (finiteSumAbsBoundBy differences bounds term-bound)
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
        (derivative-bound i))

  term-bound : ∀ i → absℝ (differences i) ≤ℝ bounds i
  term-bound i =
    subst (absℝ (differences i) ≤ℝ_)
      (sym
        (mulDistL (rat (fst ε)) bound (width partition i)))
      (differenceBoundFromRemainder
        (differences i)
        (derivative (points (FD.weakenFin i)) · width partition i)
        (rat (fst ε) · width partition i)
        (bound · width partition i)
        (subst
          (absℝ
              (differences i -
                derivative (points (FD.weakenFin i)) · width partition i)
            ≤ℝ_)
          (cong (rat (fst ε) ·_)
            (absOfNonnegative
              (width partition i) (width-nonnegative partition i)))
          (remainder-bound i (point-close i)))
        (linear-bound i))

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


-- Compatibility interface: the partition proof only needs hypotheses at
-- its nodes, so global bounds are more than sufficient.
uniformDerivativePartitionBound :
  ∀ (function derivative : ℝ → ℝ) (ε δ : ℚ₊) →
  (∀ x y →
    x ∼[ δ ] y →
    absℝ ((function y - function x) - derivative x · (y - x))
      ≤ℝ rat (fst ε) · absℝ (y - x)) →
  ∀ {a b} (partition : Partition[ a , b ]) →
  HasMeshBelow partition δ →
  ∀ bound → 0ℝ ≤ℝ bound →
  (∀ x → absℝ (derivative x) ≤ℝ bound) →
  absℝ (function b - function a) ≤ℝ
    (rat (fst ε) + bound) · (b - a)
uniformDerivativePartitionBound
    function derivative ε δ remainder-bound partition mesh
    bound 0≤bound derivative-bound =
  uniformDerivativePartitionBoundAtPoints
    function derivative ε δ partition
    (λ i → remainder-bound
      (Partition.points partition (FD.weakenFin i))
      (Partition.points partition (FD.suc i)))
    mesh bound
    (λ i → derivative-bound
      (Partition.points partition (FD.weakenFin i)))


uniformDerivativePartitionBoundOn :
  ∀ (function derivative : ℝ → ℝ) (ε δ : ℚ₊) a b →
  (∀ x y →
    a ≤ℝ x → x ≤ℝ b → a ≤ℝ y → y ≤ℝ b →
    x ∼[ δ ] y →
    absℝ ((function y - function x) - derivative x · (y - x))
      ≤ℝ rat (fst ε) · absℝ (y - x)) →
  (partition : Partition[ a , b ]) →
  HasMeshBelow partition δ →
  ∀ bound →
  (∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (derivative x) ≤ℝ bound) →
  absℝ (function b - function a) ≤ℝ
    (rat (fst ε) + bound) · (b - a)
uniformDerivativePartitionBoundOn
    function derivative ε δ a b remainder-bound partition
    mesh bound derivative-bound =
  uniformDerivativePartitionBoundAtPoints
    function derivative ε δ partition
    (λ i → remainder-bound
      (Partition.points partition (FD.weakenFin i))
      (Partition.points partition (FD.suc i))
      (partitionPointLowerBound partition (FD.weakenFin i))
      (partitionPointUpperBound partition (FD.weakenFin i))
      (partitionPointLowerBound partition (FD.suc i))
      (partitionPointUpperBound partition (FD.suc i)))
    mesh bound
    (λ i → derivative-bound
      (Partition.points partition (FD.weakenFin i))
      (partitionPointLowerBound partition (FD.weakenFin i))
      (partitionPointUpperBound partition (FD.weakenFin i)))


private
  dyadicRadius : ℕ → ℚ₊
  dyadicRadius zero = 1₊
  dyadicRadius (suc n) = (two₊ ⁻¹₊) ·₊ dyadicRadius n

  dyadicRadiusPath : ∀ n → rat (fst (dyadicRadius n)) ≡ dyadicReal n
  dyadicRadiusPath zero = refl
  dyadicRadiusPath (suc n) =
    sym (mul-rat halfℚ (fst (dyadicRadius n)))
    ∙ cong (rat halfℚ ·_) (dyadicRadiusPath n)

  dyadicRadiusTendsToZero :
    isLimitSequence (λ n → rat (fst (dyadicRadius n))) 0ℝ
  dyadicRadiusTendsToZero =
    subst (λ sequence → isLimitSequence sequence 0ℝ)
      (sym (funExt dyadicRadiusPath)) dyadicRealIsLimitZero

  -- Ordered limits remove the slack without selecting a sequence of
  -- partitions or a global differentiability modulus.
  removeMultiplicativeSlack : ∀ value bound length →
    (∀ (ε : ℚ₊) → value ≤ℝ (rat (fst ε) + bound) · length) →
    value ≤ℝ bound · length
  removeMultiplicativeSlack value bound length slack-bound =
    limitsPres≤
      (λ _ → value)
      (λ n → (rat (fst (dyadicRadius n)) + bound) · length)
      value (bound · length)
      (constantIsLimitSequence value)
      (subst
        (isLimitSequence
          (λ n → (rat (fst (dyadicRadius n)) + bound) · length))
        (cong (_· length) (addIdL bound))
        (mulPresIsLimitSequence
          (addPresIsLimitSequence dyadicRadiusTendsToZero
            (constantIsLimitSequence bound))
          (constantIsLimitSequence length)))
      (λ n → slack-bound (dyadicRadius n))


opaque
  radiuswiseUniformDerivativeBoundOn : ∀ function derivative →
    ∀ a b → a ≤ℝ b →
    IsRadiuswiseUniformDerivativeOn function derivative a b →
    ∀ bound →
    (∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (derivative x) ≤ℝ bound) →
    absℝ (function b - function a) ≤ℝ bound · (b - a)
  radiuswiseUniformDerivativeBoundOn
      function derivative a b a≤b uniformly-differentiable
      bound derivative-bound =
    removeMultiplicativeSlack
      (absℝ (function b - function a)) bound (b - a)
      (λ ε →
        PT.rec
          (isProp≤ℝ (absℝ (function b - function a))
            ((rat (fst ε) + bound) · (b - a)))
          (λ { (δ , remainder-bound) →
            PT.rec
              (isProp≤ℝ (absℝ (function b - function a))
                ((rat (fst ε) + bound) · (b - a)))
              (λ { (tagged , mesh) →
                uniformDerivativePartitionBoundOn
                  function derivative ε δ a b remainder-bound
                  (TaggedPartition.partition tagged) mesh
                  bound derivative-bound })
              (fineTaggedPartition a b a≤b δ) })
          (uniformly-differentiable ε))

  radiuswiseUniformDerivativeBound : ∀ function derivative →
    IsRadiuswiseUniformDerivative function derivative →
    ∀ a b → a ≤ℝ b →
    ∀ bound →
    (∀ x → absℝ (derivative x) ≤ℝ bound) →
    absℝ (function b - function a) ≤ℝ bound · (b - a)
  radiuswiseUniformDerivativeBound
      function derivative uniformly-differentiable a b a≤b
      bound derivative-bound =
    radiuswiseUniformDerivativeBoundOn function derivative a b a≤b
      (radiuswiseUniformDerivative→onInterval
        function derivative a b uniformly-differentiable)
      bound (λ x _ _ → derivative-bound x)
